import ExplainableCrypto.Helios.Symbolic.SourceResidualDeterminism

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- An internal move can occur only in a stage that has a matching internal
constructor. Guard success and failure are both retained, using full E. -/
theorem residual_tau_has_stage (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra) {q : Agent Empty}
    (h : Agent.Tau (residual ns swap left right extra ch phase) q) :
    ∃ next, Process.Step ns swap left right extra phase .tau next := by
  classical
  cases phase with
  | start => exact ⟨_,.receiveFirst⟩
  | firstReceived => exact (residual_firstReceived_no_tau ns swap left right extra ch hc q h).elim
  | firstPublished => exact ⟨_,.receiveSecond⟩
  | secondReceived => exact (residual_secondReceived_no_tau ns swap left right extra ch hc q h).elim
  | input rs => exact (residual_input_no_tau ns swap left right extra ch rs hr q h).elim
  | check rs r =>
    by_cases ha : Process.accepts ns swap left right rs r
    · exact ⟨_,.accept ha⟩
    · exact ⟨_,.reject ha⟩
  | rejected rs => exact (residual_rejected_no_tau ns swap left right extra ch rs q h).elim
  | sendTally rs => exact ⟨_,.sendTally⟩
  | trusteeReply rs => exact ⟨_,.receivePartial⟩
  | partialReady rs => exact (Agent.tau_output_no_step _ _ _ q h).elim
  | resultReady rs => exact (Agent.tau_output_no_step _ _ _ q h).elim
  | done rs => exact (residual_done_no_tau ns swap left right extra ch rs q h).elim

/-- Every arbitrary Tau target is parallel-equivalent to the stage successor's
literal source residual. No assumed determinism or reduction callback remains. -/
theorem residual_tau_complete (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra) {q : Agent Empty}
    (h : Agent.Tau (residual ns swap left right extra ch phase) q) :
    ∃ next, Process.Step ns swap left right extra phase .tau next ∧
      Agent.ParEq q (residual ns swap left right extra ch next) := by
  obtain ⟨next,hs⟩ := residual_tau_has_stage ns swap left right extra ch hc phase hr h
  exact ⟨next,hs,residual_tau_deterministic ns swap left right extra ch hc phase hr h
    (residual_tau_step ns swap left right extra ch hs)⟩

/-- Exact two-direction internal correspondence for the finite parallel source
layer. Visible labels, restrictions and extended substitutions remain separate. -/
theorem residual_tau_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra) (q : Agent Empty) :
    Agent.Tau (residual ns swap left right extra ch phase) q ↔
      ∃ next, Process.Step ns swap left right extra phase .tau next ∧
        Agent.ParEq q (residual ns swap left right extra ch next) := by
  constructor
  · exact residual_tau_complete ns swap left right extra ch hc phase hr
  · rintro ⟨next,hs,he⟩
    exact Agent.Tau.congr (.refl _) (residual_tau_step ns swap left right extra ch hs) he.symm

/-- Stage reachability discharges the range condition used in source inversion. -/
theorem reachable_residual_tau_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase) (q : Agent Empty) :
    Agent.Tau (residual ns swap left right extra ch phase) q ↔
      ∃ next, Process.Step ns swap left right extra phase .tau next ∧
        Agent.ParEq q (residual ns swap left right extra ch next) :=
  residual_tau_iff ns swap left right extra ch hc phase hr.wellFormed.inRange q
/-- Internal matching now holds for actual source residuals and arbitrary
parallel-equivalent representatives, in either direction between voting worlds.
This is an internal-step theorem, not labelled bisimilarity or frame secrecy. -/
theorem reachable_source_internal_matching (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : Process.Reachable ns swap left right extra phase)
    {p q target : Agent Empty} (hp : Agent.ParEq p (residual ns swap left right extra ch phase))
    (hq : Agent.ParEq q (residual ns swap' left right extra ch phase)) (h : Agent.Tau p target) :
    ∃ next, Process.Reachable ns swap left right extra next ∧
      Agent.Tau q (residual ns swap' left right extra ch next) ∧
      Agent.ParEq target (residual ns swap left right extra ch next) := by
  have hsour := Agent.Tau.congr hp.symm h (Agent.ParEq.refl _)
  obtain ⟨next,hs,he⟩ := residual_tau_complete ns swap left right extra ch hc phase hr.wellFormed.inRange hsour
  have hs' := hs.swap hf swap' hr.wellFormed.publicHistory hr.wellFormed.pendingPublic
  exact ⟨next,hr.tail ⟨.tau,hs⟩,Agent.Tau.congr hq
    (residual_tau_step ns swap' left right extra ch hs') (Agent.ParEq.refl _),he⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
