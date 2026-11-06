(*** The initial framework taken from the artifact of Arranz-Olmos et. al., "Preservation of Speculative Constant-Time by Compilation" ***)
(*** See: https://dl.acm.org/doi/10.1145/3704880 and https://artifacts.formosa-crypto.org/data/sct-preservation.tbz ***)

From Stdlib Require Import List PeanoNat Relation_Definitions.
Import ListNotations.

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
| sem_done :
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
    + intros [-> ->]. apply sem_done.
    + intros [o [os' [mi [-> [Hstep Hsem]]]]].
      eapply sem_step; eassumption.
Qed.

Lemma sem_step1 p m d o m' :
  step p m d o m' ->
  sem p m [d] [o] m'.
Proof.
  intros h.
  eapply sem_step; [exact h | apply sem_done].
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
    This : history -> directive (L := Lt) -> history;
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
      /\ sim (This h d) s' t'.

Definition initial_sim
  (p_s : prog (L := Ls))
  (p_t : prog (L := Lt))
  {hist : History}
  (sim : sim_t) :
  Prop :=
  forall inp,
    sim init_hist (initial_machine p_s inp) (initial_machine p_t inp).

Definition has_safe_bw_simulation (compile : compiler) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sim
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
      /\ sim (This h d) s' t'.

Definition has_bw_simulation (compile : compiler) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sim
      /\ step_preserves_sim p_s p_t sim Tdir Tobs.

Lemma lift_bw_simulation compile :
  has_bw_simulation compile ->
  has_safe_bw_simulation compile.
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
    (ds : list (directive (L := Lt))) :
    list (directive (L := Ls)) :=
    match ds with
    | [] => []
    | d :: ds => Tdir h d ++ Tdir_sem (This h d) ds
    end.

  Fixpoint Tobs_sem
    (h : history)
    (ds : list (directive (L := Lt)))
    (os_s : list (observation (L := Ls))) :
    list (observation (L := Lt)) :=
    match ds with
    | [] => []
    | d :: ds =>
        let n := length (Tdir h d) in
        Tobs h d (firstn n os_s) ++ Tobs_sem (This h d) ds (skipn n os_s)
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
      sem p_s s (Tdir_sem Tdir h ds) os_s s'
      /\ os_t = Tobs_sem Tdir Tobs h ds os_s.

Lemma lift_step_preserves_sim p_s p_t {_ : History} sim Tdir Tobs :
  safe_step_preserves_sim p_s p_t sim Tdir Tobs ->
  safe_sem_preserves_sim p_s p_t sim Tdir Tobs.
Proof.
  intros hbw ds.
  induction ds as [|d ds hind]; intros h os_t s t t' hsim hsafe hsem; apply semI in hsem.
  - destruct hsem as [-> ->].
    exists s, [].
    split; [apply sem_done | reflexivity].
  - destruct hsem as [o_t [os_t' [ti [-> [hstep hsem]]]]].
    destruct (hbw _ _ _ _ _ _ hsim hsafe hstep) as [s' [os_s [hsem_s [hobs hsim']]]].
    pose proof (sequential_safe_sem hsafe hsem_s) as hsafe'.
    destruct (hind _ _ _ _ _ hsim' hsafe' hsem) as [s'' [os_s' [hsem_s' ->]]].
    exists s'', (os_s ++ os_s'). simpl. split.
    + eapply sem_cat; eassumption.
    + rewrite (size_obs hsem_s), firstn_app, skipn_app, Nat.sub_diag,
        firstn_O, skipn_O, app_nil_r, firstn_all, skipn_all, <- hobs.
      reflexivity.
Qed.


(* -------------------------------------------------------------------------- *)
(* Using directives as history suffices. *)

Section DIRECTIVES_AS_HISTORY.

Let current_hist {_ : History} h := fold_left This h init_hist.
Let sim_hist {_ : History} (sim : sim_t) h := sim (current_hist h).
Let Tdir_hist {_ : History} (Tdir : Tdir_t) h := Tdir (current_hist h).
Let Tobs_hist {_ : History} (Tobs : Tobs_t) h := Tobs (current_hist h).

#[local]
Instance DirectivesHist : History :=
  {|
    history := list (directive (L := Lt));
    init_hist := [];
    This := fun h d => h ++ [d];
  |}.

Lemma directives_as_history compile :
  has_bw_simulation compile ->
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs,
      initial_sim (hist := DirectivesHist) p_s p_t sim
      /\ step_preserves_sim (hist := DirectivesHist) p_s p_t sim Tdir Tobs.
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

End DIRECTIVES_AS_HISTORY.


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
      /\ sim (This h d) s' t'.

Definition has_safe_lockstep_h_bw_simulation (compile : compiler) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists (_ : History) sim Tdir Tobs,
      initial_sim p_s p_t sim
      /\ safe_step_preserves_sim_lockstep_h p_s p_t sim Tdir Tobs.

Lemma lift_safe_lockstep_h compile :
  has_safe_lockstep_h_bw_simulation compile ->
  has_safe_bw_simulation compile.
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

Definition has_lockstep_bw_simulation (compile : compiler) :=
  forall p_s p_t,
    compile p_s p_t ->
    exists sim Tdir Tobs,
      (forall inp, sim (initial_machine p_s inp) (initial_machine p_t inp))
      /\ step_preserves_sim_lockstep p_s p_t sim Tdir Tobs.

Lemma lift_lockstep compile :
  has_lockstep_bw_simulation compile ->
  has_bw_simulation compile.
Proof.
  intros hbw p_s p_t hcomp.
  destruct (hbw p_s p_t hcomp) as [sim [Tdir [Tobs [hinit hbw']]]].
  exists
    DirectivesHist,
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
    exists t. apply sem_done.
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

Section PRESERVATION.

Context
  {input history : Type}
  {Ls Lt : Language input}
  (compile : compiler (Ls := Ls) (Lt := Lt))
.

Definition preserves_safety (phi : relation input) : Prop :=
  forall p_s p_t,
    compile p_s p_t ->
    sequential_safe_phi p_s phi ->
    sequential_safe_phi p_t phi.

Definition preserves_sct (phi : relation input) : Prop :=
  forall p_s p_t,
    compile p_s p_t ->
    sequential_safe_phi p_s phi ->
    is_sct phi p_s ->
    is_sct phi p_t.

Lemma has_safe_bw_simulation_preserves_sct phi :
  has_safe_bw_simulation compile ->
  preserves_sct phi.
Proof.
  intros hbw p_s p_t hcomp hsafe hsct ds os1 os2 inp1 inp2 out1 out2 hphi
    hsem_t1 hsem_t2.
  destruct (hbw p_s p_t hcomp) as [hist [sim [Tdir [Tobs [hinit hbw']]]]].
  pose proof (lift_step_preserves_sim hbw') as hsem.
  destruct (hsafe _ _ hphi) as [hsafe1 hsafe2].
  destruct (hsem _ _ _ _ _ _ (hinit inp1) hsafe1 hsem_t1) as [s1' [os_s1 [hsem_s1 ->]]].
  destruct (hsem _ _ _ _ _ _ (hinit inp2) hsafe2 hsem_t2) as [s2' [os_s2 [hsem_s2 ->]]].
  rewrite (hsct _ _ _ _ _ _ _ hphi hsem_s1 hsem_s2).
  reflexivity.
Qed.

End PRESERVATION.

Section COMPOSITION.

Context
  {input : Type}
  {L0 L1 L2 : Language input}
  (compile2 : compiler (Ls := L1) (Lt := L2))
  (compile1 : compiler (Ls := L0) (Lt := L1))
.

Lemma compose_safety phi :
  preserves_safety compile2 phi ->
  preserves_safety compile1 phi ->
  preserves_safety (compose compile2 compile1) phi.
Proof.
  intros hpsafe2 hpsafe1 p_s p_t [p_i h1 h2] hsafe.
  apply (hpsafe2 _ _ h2).
  exact (hpsafe1 _ _ h1 hsafe).
Qed.

Lemma compose_sct phi :
  preserves_safety compile1 phi ->
  preserves_sct compile2 phi ->
  preserves_sct compile1 phi ->
  preserves_sct (compose compile2 compile1) phi.
Proof.
  intros hpsafe hpres2 hpres1 p_s p_t [p_i h1 h2] hsafe hsct.
  apply (hpres2 _ _ h2).
  - exact (hpsafe _ _ h1 hsafe).
  - exact (hpres1 _ _ h1 hsafe hsct).
Qed.

End COMPOSITION.
