import ExplainableCrypto.Helios.Symbolic.SourceMappedCanonicalStates

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- A full phase relation with explicit base/channel coordinates and exact raw
handle-domain transport. Two worlds can share the same coordinate witnesses. -/
def CoordinatedPhaseOpening {n handles : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (e k : Nat ≃ Nat) (phase : Process.Phase) (a : Named (Fin handles)) : Prop :=
  ∃ hh : handles = phase.handles,
    Named.JointOpening (a.rename (Fin.cast hh))
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k)

variable {n handles : Nat} {ns : Names n} {swap : Bool}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
  {e k : Nat ≃ Nat} {phase : Process.Phase}

theorem CoordinatedPhaseOpening.canonical :
    CoordinatedPhaseOpening ns swap left right extra ch e k phase
      (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) := by
  refine ⟨rfl,?_⟩
  simpa only [show Fin.cast (Eq.refl phase.handles) = id from rfl,Named.rename_id,Named.mappedState] using
    Named.restrictedState_jointOpening (hidden := ch.privateChannels.image k)
      ((sourceState ns swap left right extra ch phase).mapNames e k)

theorem CoordinatedPhaseOpening.of_joint {a : Named (Fin phase.handles)}
    (h : Named.JointOpening a (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k)) :
    CoordinatedPhaseOpening ns swap left right extra ch e k phase a := by
  refine ⟨rfl,?_⟩
  simpa only [show Fin.cast (Eq.refl phase.handles) = id from rfl,Named.rename_id] using h

theorem CoordinatedPhaseOpening.structural {a b : Named (Fin handles)}
    (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a) (h : Named.Structural a b) :
    CoordinatedPhaseOpening ns swap left right extra ch e k phase b := by
  obtain ⟨hh,ha⟩ := ha
  exact ⟨hh,ha.structural_left (h.rename (Fin.cast hh) (Fin.cast_injective hh))⟩

theorem CoordinatedPhaseOpening.identity {a : Named (Fin handles)}
    (ha : PhaseJointOpening ns swap left right extra ch phase a) :
    CoordinatedPhaseOpening ns swap left right extra ch (Equiv.refl Nat) (Equiv.refl Nat) phase a := by
  obtain ⟨hh,ha⟩ := ha
  exact ⟨hh,by simpa only [Named.mappedState_identity] using ha⟩

theorem CoordinatedPhaseOpening.channels {a : Named (Fin handles)}
    (ha : CoordinatedPhaseOpening ns swap left right extra ch e k phase a) :
    a.channels = (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k).channels := by
  obtain ⟨hh,ha⟩ := ha
  simpa only [Named.channels_rename] using ha.channels

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
