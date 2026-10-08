import ExplainableCrypto.Helios.Symbolic.SourceScopedVoterElection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

theorem scopedVoterElection_reduction_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (b : Named (Fin 1)) :
    Named.Reduction (scopedVoterElection ns swap left right extra ch) b ↔
      Named.Reduction (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch .start)) b := by
  have h := scopedVoterElection_normalizes ns hf swap left right hl hr extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem scopedVoterElection_free_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels)
    (l : Extended.FreeLabel (Fin 1)) (b : Named (Fin 1)) :
    Named.FreeStep (scopedVoterElection ns swap left right extra ch) l b ↔
      Named.FreeStep (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch .start)) l b := by
  have h := scopedVoterElection_normalizes ns hf swap left right hl hr extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem scopedVoterElection_bound_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels)
    (channel : Nat) (b : Named (Option (Fin 1))) :
    Named.BoundOutput (scopedVoterElection ns swap left right extra ch) channel b ↔
      Named.BoundOutput (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch .start)) channel b := by
  have h := scopedVoterElection_normalizes ns hf swap left right hl hr extra ch
  exact ⟨fun ha => .congr h.symm ha (.refl _),fun ha => .congr h ha (.refl _)⟩

theorem scopedVoterElection_represents (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    (scopedVoterElection ns swap left right extra ch).RepresentsFrame ch.privateChannels
      (sourceView ns swap left right .start) :=
  (Named.restrictedState_represents (sourceState ns swap left right extra ch .start)).structural
    (scopedVoterElection_normalizes ns hf swap left right hl hr extra ch).symm

theorem scopedVoterElection_wellFormed (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    (scopedVoterElection ns swap left right extra ch).WellFormed :=
  (scopedVoterElection_represents ns hf swap left right hl hr extra ch).wellFormed

/-- The complete initial static clause transfers to the actual scope-bearing
voter election. Arbitrary-action matching between worlds is still separate. -/
theorem scopedVoterElection_staticEq (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    Named.StaticEq (scopedVoterElection ns false left right extra ch)
      (scopedVoterElection ns true left right extra ch) :=
  Named.reachable_structural_source_staticEq hf (.refl) ch
    (scopedVoterElection_normalizes ns hf false left right hl hr extra ch).symm
    (scopedVoterElection_normalizes ns hf true left right hl hr extra ch).symm

theorem scopedVoterElection_receivesFirst (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) :
    Named.Reduction (scopedVoterElection ns swap left right extra ch)
      (Named.restrictedState ch.privateChannels
        (sourceState ns swap left right extra ch .firstReceived)) := by
  apply (scopedVoterElection_reduction_iff ns hf swap left right hl hr extra ch _).mpr
  apply Named.restricted_tau_derivable
  exact ScopedStep.tau _ (residual_receiveFirst ns swap left right extra ch)

/-- One common fresh allocation works for arbitrary full valid ground
parameters and every finite administration size/channel allocation. -/
theorem exists_scoped_election_correspondence (left right : CandidateSubstitution n Empty) :
    ∃ ns : Names n, ns.Fresh ∧ ∀ extra ch,
      (∀ swap, Named.Structural (scopedVoterElection ns swap left right extra ch)
        (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch .start))) ∧
      Named.StaticEq (scopedVoterElection ns false left right extra ch)
        (scopedVoterElection ns true left right extra ch) := by
  obtain ⟨ns,hf,hl,hr,_⟩ := exists_parameter_fresh_election left.value right.value
  exact ⟨ns,hf,fun extra ch => ⟨fun swap => scopedVoterElection_normalizes ns hf swap left right hl hr extra ch,
    scopedVoterElection_staticEq ns hf left right hl hr extra ch⟩⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
