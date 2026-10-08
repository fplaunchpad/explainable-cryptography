import ExplainableCrypto.Helios.Symbolic.SourceElectionCommunicationMatching
import ExplainableCrypto.Helios.Symbolic.SourceGuardedActivation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
namespace Extended
variable {V : Type}

theorem InternalStep.message_communication (c : Nat) (m : Term V) (p : Agent V) (q : Agent (Option V)) :
    InternalStep .communication (.plain (.par (.output c m p) (.input c q))) (.plain (.par p (q.bind m))) := by
  let before : Agent (Option V) := .par (.output c (.var none) p.shift) ((Agent.input c q).shift)
  let after : Agent (Option V) := .par p.shift ((q.subst (liftSubst (fun v => .var (some v)))).bind (.var none))
  have hb : before.bind m = .par (.output c m p) (.input c q) := by
    change Agent.par (.output c m (p.shift.bind m)) ((Agent.input c q).shift.bind m) = _
    rw [Agent.shift_bind,Agent.shift_bind]
  have ha : after.bind m = .par p (q.bind m) := by
    change Agent.par (p.shift.bind m) (((q.subst (liftSubst (fun v => .var (some v)))).bind (.var none)).bind m) = _
    rw [Agent.shift_bind,Agent.atomic_relay_bind]
  have hbefore := (let_eliminate m before).symm
  rw [hb] at hbefore
  have hafter := let_eliminate m after
  rw [ha] at hafter
  apply InternalStep.congr hbefore ?_ hafter
  exact .newVar (.parRight _ (.atomComm c none p.shift (q.subst (liftSubst (fun v => .var (some v))))))

/-- Parallel context lifting through the two syntactic plain/extended forms. -/
theorem InternalStep.plain_parLeft {p p' : Agent V} (q : Agent V)
    (h : InternalStep .communication (.plain p) (.plain p')) :
    InternalStep .communication (.plain (.par p q)) (.plain (.par p' q)) :=
  .congr (.plainPar _ _) (.parLeft _ h) (Structural.plainPar _ _).symm

theorem InternalStep.plain_parRight (p : Agent V) {q q' : Agent V}
    (h : InternalStep .communication (.plain q) (.plain q')) :
    InternalStep .communication (.plain (.par p q)) (.plain (.par p q')) :=
  .congr (.plainPar _ _) (.parRight _ h) (Structural.plainPar _ _).symm

theorem InternalStep.ground_message_communication (V : Type) (c : Nat) (m : Ground)
    (p : Agent Empty) (q : Agent (Option Empty)) :
    InternalStep .communication (.plain (groundAgent (.par (.output c m p) (.input c q)) : Agent V))
      (.plain (groundAgent (.par p (q.bind m)))) := by
  have h := InternalStep.message_communication c (groundTerm m : Term V) (groundAgent p)
    (q.subst (liftSubst (Empty.elim : Empty → Term V)))
  simpa only [groundTerm,groundAgent,Agent.subst,Agent.bind_subst] using h

theorem InternalStep.ground_congr {p p' q q' : Agent Empty}
    (hp : Agent.ParEq p p')
    (h : InternalStep .communication (.plain (groundAgent p' : Agent V)) (.plain (groundAgent q')))
    (hq : Agent.ParEq q' q) :
    InternalStep .communication (.plain (groundAgent p : Agent V)) (.plain (groundAgent q)) :=
  .congr (parEq_derivable (hp.subst Empty.elim)) h (parEq_derivable (hq.subst Empty.elim))

end Extended

theorem Named.InternalStep.of_ground_communication (hidden : Finset Nat)
    (s t : ScopedState restricted handles) (hf : s.frame = t.frame)
    (h : Extended.InternalStep .communication
      (.plain (Extended.groundAgent s.body : Agent (Fin handles)))
      (.plain (Extended.groundAgent t.body))) :
    Named.InternalStep .communication (Named.restrictedState hidden s) (Named.restrictedState hidden t) := by
  unfold Named.restrictedState
  rw [← hf]
  exact (Named.InternalStep.embed (.parRight (Extended.activeFrame s.frame) h)).restrictNames _

theorem GuardedProgram.communicates_classified (c : Nat) (m : Term V) (sender : Agent V)
    (p : GuardedProgram (Option V)) :
    Extended.InternalStep .communication (.par (.plain (.output c m sender)) (GuardedProgram.input c p).expand)
      (.par (.plain sender) (p.subst (inputSubst m)).expand) := by
  have h := (p.subst (inputSubst m)).expand_normalizes.symm
  rw [GuardedProgram.inline_subst] at h
  exact .congr (Extended.Structural.plainPar _ _).symm
    (Extended.InternalStep.message_communication c m sender p.inline)
    ((Extended.Structural.plainPar _ _).trans (Extended.Structural.parRight _ h))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
