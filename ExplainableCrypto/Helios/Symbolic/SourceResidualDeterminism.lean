import ExplainableCrypto.Helios.Symbolic.SourceResidualQuiet

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- In-range source residuals have at most one internal successor modulo the
parallel laws. Channel separation rules out unintended private pairings. -/
theorem residual_tau_deterministic (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    (phase : Process.Phase) (hr : phase.inRange extra) {p q : Agent Empty}
    (h : Agent.Tau (residual ns swap left right extra ch phase) p)
    (h' : Agent.Tau (residual ns swap left right extra ch phase) q) : Agent.ParEq p q := by
  cases phase with
  | start =>
    unfold residual electionBody boardStart trusteeAgent at h h'
    exact Agent.tau_four_deterministic hc.honest_distinct (hc.trustee_voter 0) (hc.trustee_voter 1) h h'
  | firstReceived => exact (residual_firstReceived_no_tau ns swap left right extra ch hc p h).elim
  | firstPublished =>
    unfold residual boardSecond trusteeAgent at h h'
    exact Agent.tau_three_deterministic (hc.trustee_voter 1) h h'
  | secondReceived => exact (residual_secondReceived_no_tau ns swap left right extra ch hc p h).elim
  | input rs => exact (residual_input_no_tau ns swap left right extra ch rs hr p h).elim
  | check rs r =>
    unfold residual trusteeAgent at h h'
    exact Agent.tau_branch_input_deterministic h h'
  | rejected rs => exact (residual_rejected_no_tau ns swap left right extra ch rs p h).elim
  | sendTally rs =>
    unfold residual boardFinish trusteeAgent at h h'
    exact Agent.tau_pair_deterministic h h'
  | trusteeReply rs =>
    have hh := Agent.Tau.congr (Agent.ParEq.comm _ _) h (Agent.ParEq.refl _)
    have hh' := Agent.Tau.congr (Agent.ParEq.comm _ _) h' (Agent.ParEq.refl _)
    exact Agent.tau_pair_deterministic hh hh'
  | partialReady rs => exact (Agent.tau_output_no_step _ _ _ p h).elim
  | resultReady rs => exact (Agent.tau_output_no_step _ _ _ p h).elim
  | done rs => exact (residual_done_no_tau ns swap left right extra ch rs p h).elim
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
