import ExplainableCrypto.Helios.Symbolic.SourceElectionOpeningInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- The complete opening invariant at a phase, with explicit equality of the
raw public domain and that phase's canonical handle domain. -/
def PhaseOpening {n handles : Nat} (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels)
    (phase : Process.Phase) (a : Named (Fin handles)) : Prop :=
  ∃ hh : handles = phase.handles,
    Named.HasCanonicalOpening (a.rename (Fin.cast hh)) (sourceView ns swap left right phase)
      (residual ns swap left right extra ch phase)

variable {n handles : Nat} {ns : Names n} {swap : Bool}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
  {phase : Process.Phase}

theorem PhaseOpening.canonical :
    PhaseOpening ns swap left right extra ch phase
      (Named.restrictedState ch.privateChannels (sourceState ns swap left right extra ch phase)) := by
  refine ⟨rfl,?_⟩
  simpa only [show Fin.cast (Eq.refl phase.handles) = id from rfl,Named.rename_id,sourceState] using
    Named.restrictedState_hasCanonicalOpening (hidden := ch.privateChannels)
      (sourceState ns swap left right extra ch phase)

theorem PhaseOpening.structural {a b : Named (Fin handles)}
    (ha : PhaseOpening ns swap left right extra ch phase a) (h : Named.Structural a b) :
    PhaseOpening ns swap left right extra ch phase b := by
  obtain ⟨hh,ha⟩ := ha
  exact ⟨hh,ha.structural (h.rename (Fin.cast hh) (Fin.cast_injective hh))⟩

theorem PhaseOpening.internal {a b : Named (Fin handles)}
    (ha : PhaseOpening ns swap left right extra ch phase a) (hc : ch.Fresh)
    (hr : phase.inRange extra) (h : Named.Reduction a b) :
    ∃ next, Process.Step ns swap left right extra phase .tau next ∧
      PhaseOpening ns swap left right extra ch next b := by
  obtain ⟨hh,ha⟩ := ha
  obtain ⟨next,hj,hs,hb⟩ := source_opening_internal_next ns swap left right extra ch hc phase hr ha
    (h.cast_handles hh)
  refine ⟨next,hs,hh.trans hj,?_⟩
  have he : Fin.cast hj ∘ Fin.cast hh = Fin.cast (hh.trans hj) := by funext i; rfl
  simpa only [Named.rename_comp,he] using hb

/-- Any finite sequence of actual Named internal actions has a corresponding
stage-internal sequence, retaining the full invariant on its final raw target.
No intermediate raw target needs a canonical Structural presentation. -/
theorem PhaseOpening.internal_trace {a b : Named (Fin handles)}
    (ha : PhaseOpening ns swap left right extra ch phase a) (hc : ch.Fresh)
    (hr : Process.Reachable ns swap left right extra phase)
    (h : Relation.ReflTransGen (@Named.Reduction (Fin handles)) a b) :
    ∃ next, Process.Reachable ns swap left right extra next ∧
      Relation.ReflTransGen (fun p q => Process.Step ns swap left right extra p .tau q) phase next ∧
      PhaseOpening ns swap left right extra ch next b := by
  induction h with
  | refl => exact ⟨phase,hr,.refl,ha⟩
  | tail h hstep ih =>
    obtain ⟨current,hr',ht,ha'⟩ := ih
    obtain ⟨next,hs,hb⟩ := ha'.internal hc hr'.wellFormed.inRange hstep
    exact ⟨next,hr'.tail ⟨.tau,hs⟩,ht.tail hs,hb⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
