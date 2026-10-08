import ExplainableCrypto.Helios.Symbolic.SourceNamedLabelScope
import ExplainableCrypto.Helios.Symbolic.SourceFreshBoundPrenex
import ExplainableCrypto.Helios.Symbolic.SourceFreshOperationalPrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Structural factorization into an outer name prefix preserves complete
variable-domain coverage and unique definitions in the actual Extended body. -/
theorem Structural.prenex_body_wellFormed {a : Named V} {ns : List SourceName} {b : Extended V}
    (h : Structural a (Named.restrictNames ns (.embed b)))
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) :
    b.WellFormed ∧ ∀ v, b.Exports v := by
  have hb : b.UniqueDefinitions := (restrictNames_uniqueDefinitions ns _).mp (h.uniqueDefinitions.mp hu)
  have he : ∀ v, b.Exports v := fun v => (restrictNames_exports ns _ v).mp ((h.exports v).mp (ha v))
  exact ⟨⟨hb,Extended.closed_of_all_exports b he⟩,he⟩

theorem Reduction.prenex_wellFormed {a b : Named V} (h : Reduction a b)
    (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.Reduction a' b' ∧
      a'.WellFormed ∧ b'.WellFormed ∧ (∀ v, a'.Exports v) ∧ (∀ v, b'.Exports v) := by
  obtain ⟨ns,a',b',hs,ht,hr⟩ := h.prenex
  obtain ⟨hwa,hea⟩ := hs.prenex_body_wellFormed hu ha
  obtain ⟨hwb,heb⟩ := ht.prenex_body_wellFormed (h.uniqueDefinitions.mp hu) (fun v => (h.exports v).mp (ha v))
  exact ⟨ns,a',b',hs,ht,hr,hwa,hwb,hea,heb⟩

theorem FreeStep.prenex_wellFormed {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) :
    ∃ (ns : List SourceName) (a' b' : Extended V),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.FreeStep a' l b' ∧
      (∀ n ∈ ns, n ∉ l.nameSupport) ∧ a'.WellFormed ∧ b'.WellFormed ∧
      (∀ v, a'.Exports v) ∧ (∀ v, b'.Exports v) ∧ l.VarsIn a'.Exports := by
  obtain ⟨ns,a',b',hs,ht,hr,hf⟩ := h.prenex
  obtain ⟨hwa,hea⟩ := hs.prenex_body_wellFormed hu ha
  obtain ⟨hwb,heb⟩ := ht.prenex_body_wellFormed (h.uniqueDefinitions.mp hu) (fun v => (h.exports v).mp (ha v))
  exact ⟨ns,a',b',hs,ht,hr,hf,hwa,hwb,hea,heb,l.varsIn_of_all hea⟩

theorem BoundOutput.prenex_wellFormed {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (hu : a.UniqueDefinitions) (ha : ∀ v, a.Exports v) :
    ∃ (ns : List SourceName) (a' : Extended V) (b' : Extended (Option V)),
      Structural a (Named.restrictNames ns (.embed a')) ∧
      Structural b (Named.restrictNames ns (.embed b')) ∧ Extended.BoundOutput a' c b' ∧
      (∀ n ∈ ns, n ≠ SourceName.channel c) ∧ a'.WellFormed ∧ b'.WellFormed ∧
      (∀ v, a'.Exports v) ∧ (∀ v, b'.Exports v) := by
  obtain ⟨ns,a',b',hs,ht,hr,hf⟩ := h.prenex
  obtain ⟨hwa,hea⟩ := hs.prenex_body_wellFormed hu ha
  obtain ⟨hwb,heb⟩ := ht.prenex_body_wellFormed (h.uniqueDefinitions hu) (h.all_exports hu ha)
  exact ⟨ns,a',b',hs,ht,hr,hf,hwa,hwb,hea,heb⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
