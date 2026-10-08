import ExplainableCrypto.Helios.Symbolic.SourceChannelPolicy
import ExplainableCrypto.Helios.Symbolic.SourceTauShapes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem residual_firstReceived_no_tau (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (q : Agent Empty) :
    ¬ Agent.Tau (residual ns swap left right extra ch .firstReceived) q := by
  dsimp only [residual,trusteeAgent]
  exact Agent.tau_two_outputs_input_no_step (Ne.symm (hc.trustee_voter 1)) hc.broadcast_trustee

theorem residual_secondReceived_no_tau (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (hc : ch.Fresh) (q : Agent Empty) :
    ¬ Agent.Tau (residual ns swap left right extra ch .secondReceived) q := by
  dsimp only [residual,trusteeAgent]
  exact Agent.tau_output_input_no_step hc.broadcast_trustee

/-- The voter-count premise is necessary: an exhausted collection body sends
a tally, whereas an in-range input phase must actually wait for its voter. -/
theorem residual_input_no_tau (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (extra : Nat) (ch : Channels) (rs : List (Recipe 3)) (hr : rs.length < extra) (q : Agent Empty) :
    ¬ Agent.Tau (residual ns swap left right extra ch (.input rs)) q := by
  have he : extra-rs.length=(extra-rs.length-1)+1 := by omega
  dsimp only [residual,trusteeAgent]
  rw [he,collectBallots]
  exact Agent.tau_two_inputs_no_step
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
