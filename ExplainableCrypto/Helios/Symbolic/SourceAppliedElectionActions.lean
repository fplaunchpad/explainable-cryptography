import ExplainableCrypto.Helios.Symbolic.SourceOpenElectionApplication

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem instantiatedElection_reduction_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a)
    (b : Named (Fin 1)) :
    Named.Reduction a b ↔ Named.Reduction
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) b := by
  have h := instantiatedElection_normalizes ns hf left right hp swap extra ch ha
  exact ⟨fun j => .congr h.symm j (.refl _),fun j => .congr h j (.refl _)⟩

theorem instantiatedElection_free_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a)
    (l : Extended.FreeLabel (Fin 1)) (b : Named (Fin 1)) :
    Named.FreeStep a l b ↔ Named.FreeStep
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) l b := by
  have h := instantiatedElection_normalizes ns hf left right hp swap extra ch ha
  exact ⟨fun j => .congr h.symm j (.refl _),fun j => .congr h j (.refl _)⟩

theorem instantiatedElection_bound_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a)
    (channel : Nat) (b : Named (Option (Fin 1))) :
    Named.BoundOutput a channel b ↔ Named.BoundOutput
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start)) channel b := by
  have h := instantiatedElection_normalizes ns hf left right hp swap extra ch ha
  exact ⟨fun j => .congr h.symm j (.refl _),fun j => .congr h j (.refl _)⟩

theorem instantiatedElection_represents (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a) :
    a.RepresentsFrame ch.privateChannels (sourceView ns swap left right .start) :=
  (Named.restrictedState_represents (sourceState ns swap left right extra ch .start)).structural
    (instantiatedElection_normalizes ns hf left right hp swap extra ch ha).symm

theorem instantiatedElection_wellFormed (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a) :
    a.WellFormed := (instantiatedElection_represents ns hf left right hp swap extra ch ha).wellFormed

/-- Both processes must be actual instantiations of the same open election;
the full initial static clause follows with the real source frame witnesses. -/
theorem instantiatedElection_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (extra : Nat) (ch : Channels) {a b : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst false left right) (openElectionTemplate ns extra ch) a)
    (hb : Named.Instantiates (electionCandidateSubst true left right) (openElectionTemplate ns extra ch) b) :
    Named.StaticEq a b :=
  Named.reachable_structural_source_staticEq hf (.refl) ch
    (instantiatedElection_normalizes ns hf left right hp false extra ch ha).symm
    (instantiatedElection_normalizes ns hf left right hp true extra ch hb).symm

theorem instantiatedElection_receivesFirst (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hp : ElectionParametersFresh ns left right)
    (swap : Bool) (extra : Nat) (ch : Channels) {a : Named (Fin 1)}
    (ha : Named.Instantiates (electionCandidateSubst swap left right) (openElectionTemplate ns extra ch) a) :
    Named.Reduction a
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .firstReceived)) := by
  apply (instantiatedElection_reduction_iff ns hf left right hp swap extra ch ha _).mpr
  apply Named.restricted_tau_derivable
  exact ScopedStep.tau _ (residual_receiveFirst ns swap left right extra ch)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
