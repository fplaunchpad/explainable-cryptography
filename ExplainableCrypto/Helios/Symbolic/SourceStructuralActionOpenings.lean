import ExplainableCrypto.Helios.Symbolic.SourcePairedOpeningReduction
import ExplainableCrypto.Helios.Symbolic.SourcePairedVisibleOpenings

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- A sufficiently fresh chosen opening retains an actual internal action
between its embedded body and an actual opening of the complete target. -/
theorem Reduction.opening_named_step {a b : Named V} (h : Reduction a b) :
    ∃ needed : Finset SourceName,
      ∀ (avoid : Finset SourceName) (ns : List SourceName) (a' : Extended V),
        Opens a NameAssignment.literal ns a' → (∀ n ∈ ns, n ∉ avoid ∪ needed) →
        ∃ (ms : List SourceName) (b' : Extended V),
          Opens b NameAssignment.literal ms b' ∧
          Reduction (.embed a') (.embed b') ∧ (∀ n ∈ ms, n ∉ avoid ∪ needed) := by
  obtain ⟨needed,ht⟩ := h.opening_binder_step
  refine ⟨needed,?_⟩
  intro avoid ns a' ho hf
  obtain ⟨c,d,ms,b',hr,hs,hb,ht,hfresh⟩ := ht avoid ns a' ho hf
  exact ⟨ms,b',hb,.congr hs.named (.embed hr) ht.named,hfresh⟩

/-- The original input or existing-handle output label is retained exactly. -/
theorem FreeStep.opening_named_step {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (ms : List SourceName) (b' : Extended V),
      Opens b NameAssignment.literal ms b' ∧
      FreeStep (.embed a') l (.embed b') ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨c,d,ms,b',hr,hs,hb,ht,hfresh⟩ := h.opening_binder_step avoid ho hf
  exact ⟨ms,b',hb,.congr hs.named (.embed hr) ht.named,hfresh⟩

/-- The original channel and full fresh-variable target survive opening. -/
theorem BoundOutput.opening_named_step {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (avoid : Finset SourceName) {ns : List SourceName} {a' : Extended V}
    (ho : Opens a NameAssignment.literal ns a') (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ (ms : List SourceName) (b' : Extended (Option V)),
      Opens b NameAssignment.literal ms b' ∧
      BoundOutput (.embed a') c (.embed b') ∧ (∀ n ∈ ms, n ∉ avoid) := by
  obtain ⟨d,t,ms,b',hr,hs,hb,ht,hfresh⟩ := h.opening_binder_step avoid ho hf
  exact ⟨ms,b',hb,.congr hs.named (.embed hr) ht.named,hfresh⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
