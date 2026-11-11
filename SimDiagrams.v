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
      list directive ->
      list observation ->
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
    forall m m' m'' ds1 os1 ds2 os2,
      step p m ds1 os1 m' ->
      sem p m' ds2 os2 m'' ->
      sem p m (ds1 ++ ds2) (os1 ++ os2) m''
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
  sem p m ds os m' ->
  (ds = [] /\ os = [] /\ m' = m)
  \/ exists ds1 os1 mi ds2 os2,
       ds = ds1 ++ ds2 /\ os = os1 ++ os2
       /\ step p m ds1 os1 mi /\ sem p mi ds2 os2 m'.
Proof.
  intros H. destruct H as [m0 | m0 mi m0' ds1 os1 ds2 os2 Hstep Hsem].
  - left. repeat split.
  - right. exists ds1, os1, mi, ds2, os2. repeat split; assumption.
Qed.

Lemma sem_step1 p m ds os m' :
  step p m ds os m' ->
  sem p m ds os m'.
Proof.
  intros h.
  pose proof (sem_step h (sem_refl p m')) as H.
  rewrite !app_nil_r in H.
  exact H.
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
  - rewrite <- !app_assoc.
    eapply sem_step; [eassumption|].
    apply IHsem; assumption.
Qed.

End FACTS.

Definition comparable {A : Type} (l1 l2 : list A) : Prop :=
  prefix l1 l2 \/ prefix l2 l1.

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

  Lemma sequential_safe_step p m m' ds os :
    sequential_safe p m ->
    step p m ds os m' ->
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
    list (directive (L := Lt)) ->
    list (directive (L := Ls)).

  Definition Tobs_t0 : Type :=
    history ->
    list (directive (L := Lt)) ->
    list (observation (L := Ls)) ->
    list (observation (L := Lt)).

  Definition arity_t0 : Type :=
    history ->
    nat.

  Definition oarity_t0 : Type :=
    history ->
    list (directive (L := Lt)) ->
    nat.

End HISTORY.

Class History :=
  {
    history : Type;
    init_hist : history;
    This :
      history ->
      list (directive (L := Lt)) ->
      list (observation (L := Lt)) ->
      history;
  }.

Definition sim_t {hist : History} := Eval hnf in sim_t0 history.
Definition Tdir_t {hist : History} := Eval hnf in Tdir_t0 history.
Definition Tobs_t {hist : History} := Eval hnf in Tobs_t0 history.
Definition arity_t {hist : History} := Eval hnf in arity_t0 history.
Definition oarity_t {hist : History} := Eval hnf in oarity_t0 history.

Definition safe_step_preserves_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : Tdir_t)
  (Tobs : Tobs_t)
  (arity : arity_t)
  (oarity : oarity_t) :
  Prop :=
  forall ds h os_t s t t',
    sim h s t ->
    sequential_safe p_s s ->
    step p_t t ds os_t t' ->
    length ds = arity h
    /\ exists s' os_s,
         sem p_s s (Tdir h ds) os_s s'
         /\ length os_s = oarity h ds
         /\ os_t = Tobs h ds os_s
         /\ sim (This h ds os_t) s' t'.

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
    exists (_ : History) sim Tdir Tobs arity oarity,
      initial_sim p_s p_t sync sim
      /\ safe_step_preserves_sim p_s p_t sim Tdir Tobs arity oarity.


(* -------------------------------------------------------------------------- *)
(* Most passes don't need safety. *)

Definition step_preserves_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t)
  (Tdir : Tdir_t)
  (Tobs : Tobs_t)
  (arity : arity_t)
  (oarity : oarity_t) :
  Prop :=
  forall ds h os_t s t t',
    sim h s t ->
    step p_t t ds os_t t' ->
    length ds = arity h
    /\ exists s' os_s,
         sem p_s s (Tdir h ds) os_s s'
         /\ length os_s = oarity h ds
         /\ os_t = Tobs h ds os_s
         /\ sim (This h ds os_t) s' t'.

Definition has_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs arity oarity,
      initial_sim p_s p_t sync sim
      /\ step_preserves_sim p_s p_t sim Tdir Tobs arity oarity.

Lemma lift_bw_simulation compile sync :
  has_bw_simulation compile sync ->
  has_safe_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [arity [oarity [hinit hbw']]]]]]].
  exists hist, sim, Tdir, Tobs, arity, oarity.
  split; [exact hinit|].
  intros ds h os_t s t t' hsim _ hstep.
  exact (hbw' ds h os_t s t t' hsim hstep).
Qed.


(* -------------------------------------------------------------------------- *)
(* Using directives and observations as history suffices. *)

Section TRACE_AS_HISTORY.

Let current_hist {_ : History}
  (h : list (list (directive (L := Lt)) * list (observation (L := Lt)))) :=
  fold_left (fun h0 dobs => This h0 (fst dobs) (snd dobs)) h init_hist.
Let sim_hist {_ : History} (sim : sim_t) h := sim (current_hist h).
Let Tdir_hist {_ : History} (Tdir : Tdir_t) h := Tdir (current_hist h).
Let Tobs_hist {_ : History} (Tobs : Tobs_t) h := Tobs (current_hist h).
Let arity_hist {_ : History} (arity : arity_t) h := arity (current_hist h).
Let oarity_hist {_ : History} (oarity : oarity_t) h := oarity (current_hist h).

#[local]
Instance TraceHist : History :=
  {|
    history := list (list (directive (L := Lt)) * list (observation (L := Lt)));
    init_hist := [];
    This := fun h ds os => h ++ [(ds, os)];
  |}.

Lemma trace_as_history compile sync :
  has_bw_simulation compile sync ->
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs arity oarity,
      initial_sim (hist := TraceHist) p_s p_t sync sim
      /\ step_preserves_sim (hist := TraceHist) p_s p_t sim Tdir Tobs arity oarity.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [arity [oarity [hinit hbw']]]]]]].
  exists (sim_hist sim), (Tdir_hist Tdir), (Tobs_hist Tobs),
    (arity_hist arity), (oarity_hist oarity).
  split; [exact hinit|].
  intros ds h os_t s t t' hsim hstep_t.
  destruct (hbw' _ _ _ _ _ _ hsim hstep_t)
    as [hlen [s' [os_s [hsem_s [holen [hobs hsim']]]]]].
  split; [exact hlen|].
  exists s', os_s.
  split; [exact hsem_s|].
  split; [exact holen|].
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
  (Tdir : Tdir_t)
  (Tobs : Tobs_t)
  (arity : arity_t)
  (oarity : oarity_t) :
  Prop :=
  forall ds h os_t s t t',
    sim h s t ->
    sequential_safe p_s s ->
    step p_t t ds os_t t' ->
    length ds = arity h
    /\ exists s' os_s,
         step p_s s (Tdir h ds) os_s s'
         /\ length os_s = oarity h ds
         /\ os_t = Tobs h ds os_s
         /\ sim (This h ds os_t) s' t'.

Definition has_safe_lockstep_h_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs arity oarity,
      initial_sim p_s p_t sync sim
      /\ safe_step_preserves_sim_lockstep_h p_s p_t sim Tdir Tobs arity oarity.

Lemma lift_safe_lockstep_h compile sync :
  has_safe_lockstep_h_bw_simulation compile sync ->
  has_safe_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [arity [oarity [hinit hbw']]]]]]].
  exists hist, sim, Tdir, Tobs, arity, oarity.
  split; [exact hinit|].
  intros ds h os_t s t t' hsim hsafe hstep_t.
  destruct (hbw' _ _ _ _ _ _ hsim hsafe hstep_t)
    as [hlen [s' [os_s [hstep_s [holen [hobs hsim']]]]]].
  split; [exact hlen|].
  exists s', os_s.
  split; [apply sem_step1; exact hstep_s|].
  split; [exact holen|].
  split; [exact hobs | exact hsim'].
Qed.


(* -------------------------------------------------------------------------- *)
(* Lock-step simulations without history. *)

Definition step_preserves_sim_lockstep
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  (sim : machine (L := Ls) -> machine (L := Lt) -> Prop)
  (Tdir : list (directive (L := Lt)) -> list (directive (L := Ls)))
  (Tobs : list (observation (L := Ls)) -> list (observation (L := Lt)))
  (arity : nat)
  (oarity : list (directive (L := Lt)) -> nat) :
  Prop :=
  forall ds os_t s t t',
    sim s t ->
    step p_t t ds os_t t' ->
    length ds = arity
    /\ exists s' os_s,
         step p_s s (Tdir ds) os_s s'
         /\ length os_s = oarity ds
         /\ os_t = Tobs os_s
         /\ sim s' t'.

Definition has_lockstep_bw_simulation (compile : compiler) (sync : input_sync) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs arity oarity,
      (forall inp inp',
          sync p_s inp inp' ->
          sim (initial_machine p_s inp) (initial_machine p_t inp'))
      /\ step_preserves_sim_lockstep p_s p_t sim Tdir Tobs arity oarity.

Lemma lift_lockstep compile sync :
  has_lockstep_bw_simulation compile sync ->
  has_bw_simulation compile sync.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [sim [Tdir [Tobs [arity [oarity [hinit hbw']]]]]].
  exists
    TraceHist,
    (fun _ => sim),
    (fun _ ds => Tdir ds),
    (fun _ _ os => Tobs os),
    (fun _ => arity),
    (fun _ ds => oarity ds).
  split; [exact hinit|].
  intros ds h os_t s t t' hsim hstep_t.
  destruct (hbw' _ _ _ _ _ hsim hstep_t)
    as [hlen [s' [os_s [hstep_s [holen [hobs hsim']]]]]].
  split; [exact hlen|].
  exists s', os_s.
  split; [apply sem_step1; exact hstep_s|].
  split; [exact holen|].
  split; [exact hobs | exact hsim'].
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
    forall ds s os s' t,
      R s t ->
      step p_s s (map Tdir ds) os s' ->
      exists2 t', step p_t t ds (map Tobs os) t' & R s' t'
  }.

Context (diag: forward_lock_step_simulation_diagram).

Definition forward_semantics_preservation : Prop :=
  forall inp ds os s,
    sem_p p_s inp (map Tdir ds) os s ->
    exists t, sem_p p_t inp ds (map Tobs os) t.

Lemma forward_lock_step_to_full_trace : forward_semantics_preservation.
Proof.
  intros inp ds os s' H.
  unfold sem_p in *.
  pose proof (fls_init diag inp) as r.
  revert r.
  generalize (initial_machine p_t inp) as t.
  revert H.
  generalize (initial_machine p_s inp) as s.
  intros s H.
  remember (map Tdir ds) as D eqn:HD.
  revert ds HD.
  induction H as [s | s mi s'' D1 O1 D2 O2 step_s sem_s IH]; intros ds HD t r.
  - exists t.
    destruct ds as [|d ds]; [apply sem_refl | simpl in HD; discriminate HD].
  - symmetry in HD.
    apply map_eq_app in HD as [ds1 [ds2 [-> [HD1 HD2]]]].
    rewrite <- HD1 in step_s.
    destruct (fls_step diag r step_s) as [t' step_t r'].
    destruct (IH ds2 (eq_sym HD2) t' r') as [tf exec_t].
    exists tf.
    rewrite map_app.
    eapply sem_step; eassumption.
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
      comparable os1 os2.

End OBSERVATIONAL_EQUIVALENCE.

(* --- phi-SCT inputs imply same observations, easy *)
Lemma is_sct_same_obs {input : Type} {L : Language input} (phi : relation input) (p : prog (L := L)) (inp1 inp2 : input):
  is_sct phi p -> phi inp1 inp2 -> same_obs p inp1 inp2.
Proof.
  intros Hsct Hphi ds os1 os2 out1 out2 Hsem1 Hsem2.
  exact (Hsct ds os1 os2 inp1 inp2 out1 out2 Hphi Hsem1 Hsem2).
Qed.

(* --- same observations on inp1 and inp2 imply phi-SCT on exactly this inputs *)
Lemma same_obs_is_sct {input : Type} {L : Language input} (p : prog (L := L)) inp1 inp2 :
  same_obs p inp1 inp2 ->
  is_sct (fun a b => a = inp1 /\ b = inp2) p.
Proof.
  intros Hso ds os1 os2 a b out1 out2 [-> ->] Hsem1 Hsem2.
  exact (Hso _ _ _ _ _ Hsem1 Hsem2).
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
        * apply Hsafe1.
        * apply Hsafe2.
      + exact (same_obs_is_sct Hsameobs).
    - exists inp1, inp2. auto.
  Qed.
End SCT_PRESERVATION_RELSEC.
