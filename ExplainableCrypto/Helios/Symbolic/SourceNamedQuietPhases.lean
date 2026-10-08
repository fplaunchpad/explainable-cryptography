import ExplainableCrypto.Helios.Symbolic.SourceElectionConditionalLocation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem named_noncheck_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (hn : ∀ rs r, phase ≠ .check rs r)
    (ht : ∀ q, ¬ Agent.Tau (residual ns swap left right extra ch phase) q)
    {a b : Named (Fin phase.handles)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) a) :
    ¬ Named.Reduction a b := by
  apply Named.no_reduction_of_quiet_interpretation NameAssignment.literal _
    (ha.canonical_interprets (sourceState ns swap left right extra ch phase)) _ ht
  intro h
  obtain ⟨rs,r,he⟩ := (residual_hasConditional_iff ns swap left right extra ch phase).mp h
  exact hn rs r he

theorem named_firstReceived_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a b : Named (Fin 1)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .firstReceived)) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch .firstReceived (by intros; simp)
    (residual_firstReceived_no_tau ns swap left right extra ch hc) ha

theorem named_secondReceived_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a b : Named (Fin 2)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .secondReceived)) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch .secondReceived (by intros; simp)
    (residual_secondReceived_no_tau ns swap left right extra ch hc) ha

theorem named_input_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) (hr : rs.length < extra) {a b : Named (Fin 3)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.input rs))) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch (.input rs) (by intros; simp)
    (residual_input_no_tau ns swap left right extra ch rs hr) ha

theorem named_partialReady_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) {a b : Named (Fin 3)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.partialReady rs))) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch (.partialReady rs) (by intros; simp)
    (Agent.tau_output_no_step _ _ _) ha

theorem named_resultReady_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) {a b : Named (Fin 4)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.resultReady rs))) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch (.resultReady rs) (by intros; simp)
    (Agent.tau_output_no_step _ _ _) ha

theorem named_done_no_reduction (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (rs : List (Recipe 3)) {a b : Named (Fin 5)}
    (ha : Named.Structural
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch (.done rs))) a) :
    ¬ Named.Reduction a b :=
  named_noncheck_no_reduction ns swap left right extra ch (.done rs) (by intros; simp)
    (residual_done_no_tau ns swap left right extra ch rs) ha

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
