import ExplainableCrypto.Helios.Symbolic.SourceElectionSilent

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Source channels are pairwise distinct. This is a naming condition only;
restriction and the visible-action policy must be enforced by separate
operational rules. -/
structure Channels.Fresh (ch : Channels) : Prop where
  voters : Function.Injective ch.voter
  broadcast_voter : ∀ i, ch.broadcast ≠ ch.voter i
  trustee_voter : ∀ i, ch.trustee ≠ ch.voter i
  broadcast_trustee : ch.broadcast ≠ ch.trustee

theorem Channels.canonical_fresh : Channels.canonical.Fresh := by
  constructor
  · intro i j h
    change i+2=j+2 at h
    omega
  · intro i
    change 0 ≠ i+2
    omega
  · intro i
    change 1 ≠ i+2
    omega
  · decide

theorem Channels.Fresh.honest_distinct {ch : Channels} (h : ch.Fresh) :
    ch.voter 0 ≠ ch.voter 1 := by
  intro he
  have hh := h.voters he
  omega
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
