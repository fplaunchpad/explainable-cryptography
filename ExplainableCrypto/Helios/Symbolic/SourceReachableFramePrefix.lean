import ExplainableCrypto.Helios.Symbolic.SourceVariableFramePrefix
import ExplainableCrypto.Helios.Symbolic.SourceReachableElectionPhases

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- Original heterogeneous execution preserves complete public providers and
unique definitions. Bound outputs and bijective reindexing retain exact domains. -/
theorem Execution.complete_definitions {a : Named V} {b : Named W} (h : Execution a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) :
    b.UniqueDefinitions ∧ ∀ v, b.Exports v := by
  induction h with
  | refl => exact ⟨hu,ha⟩
  | structural h => exact ⟨h.uniqueDefinitions.mp hu,fun v => (h.exports v).mp (ha v)⟩
  | internal h => exact ⟨h.uniqueDefinitions.mp hu,fun v => (h.exports v).mp (ha v)⟩
  | free h => exact ⟨h.uniqueDefinitions.mp hu,fun v => (h.exports v).mp (ha v)⟩
  | bound h => exact ⟨h.uniqueDefinitions hu,h.all_exports hu ha⟩
  | reindex a e =>
    refine ⟨(a.uniqueDefinitions_rename_iff e e.injective).mpr hu,?_⟩
    intro v
    exact (a.rename_exports_iff e v).mpr ⟨e.symm v,e.apply_symm_apply v,ha _⟩
  | trans _ _ ih ij =>
    obtain ⟨hb,hc⟩ := ih hu ha
    exact ij hb hc

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat} {V : Type}

/-- Every raw historical execution has both a reached phase and a structurally
extracted complete finite provider forest on that phase's exact public domain.
Initial extraction, name freshness and provider coverage are all derived.
The forest's equations are not yet solved to a ground frame presentation. -/
theorem scopedVoterElection_execution_frame_prefix (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh)
    {a : Named V} (h : Named.Execution (scopedVoterElection ns swap left right extra ch) a)
    (avoid : Finset SourceName) :
    ∃ (phase : Process.Phase) (e k : Nat ≃ Nat) (i : V ≃ Fin phase.handles),
      Process.Reachable ns swap left right extra phase ∧
      Named.JointOpening (a.rename i)
        (Named.mappedState ch.privateChannels (sourceState ns swap left right extra ch phase) e k) ∧
      ∃ (names : List SourceName) (locals : Nat)
        (d : Extended (Extended.LocalVars locals (Fin phase.handles))),
        d.FrameForest ∧ d.UniqueDefinitions ∧ (∀ v, d.Exports v) ∧
        (∀ x ∈ names, x ∉ avoid ∪ (a.rename i).frameOf.allNames) ∧
        Named.Structural (a.rename i).frameOf
          (Named.restrictNames names (.embed (Extended.closeVars locals d))) := by
  obtain ⟨phase,e,k,i,hphase,hjoint⟩ :=
    scopedVoterElection_execution_phase ns hf swap left right hl hr extra ch hc h
  have hp := scopedVoterElection_represents ns hf swap left right hl hr extra ch
  obtain ⟨hu,ha⟩ := (h.trans (.reindex a i)).complete_definitions hp.wellFormed.1 hp.all_exports
  exact ⟨phase,e,k,i,hphase,hjoint,(a.rename i).exists_complete_frame_prefix hu ha avoid⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
