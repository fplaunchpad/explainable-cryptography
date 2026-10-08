import ExplainableCrypto.Helios.Symbolic.SourceExtendedSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceNamedPresentationNames

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- General substitution into an embedded Extended context retains its
provider and both syntactic parallel presentations. -/
theorem Structural.substEmbedded (x : V) (m : Term V) (a : Extended V) (ha : ¬ a.Exports x) :
    Structural (.par (.embed (.active x m)) (.embed a))
      (.par (.embed (.active x m)) (.embed (a.substFree x m))) :=
  (Structural.embedPar _ _).symm.trans
    ((Structural.embed (Extended.Structural.substExtended x m a ha)).trans (Structural.embedPar _ _))

/-- Capture-avoiding Subst for any current Named context: first expose a fresh
name prefix around an Extended body, then substitute there. The original full
replacement stays fixed, and no prefix binder captures any of its names. -/
theorem Structural.substNamed_fresh (x : V) (m : Term V) (a : Named V) (ha : ¬ a.Exports x) :
    ∃ (ns : List SourceName) (b : Extended V),
      Structural a (Named.restrictNames ns (.embed b)) ∧ ¬ b.Exports x ∧
      (∀ n ∈ ns, n ∉ (Extended.active x m).nameSupport) ∧
      Structural (.par (.embed (.active x m)) a)
        (.par (.embed (.active x m)) (Named.restrictNames ns (.embed (b.substFree x m)))) := by
  obtain ⟨ns,b,hb,hf⟩ := exists_fresh_prenex a (Extended.active x m).nameSupport
  have hn : ¬ b.Exports x := fun h => ha ((hb.exports x).mpr ((restrictNames_exports ns _ x).mpr h))
  refine ⟨ns,b,hb,hn,hf,?_⟩
  exact (Structural.parRight _ hb).trans
    ((Structural.par_restrictNames_right (.embed (.active x m)) (.embed b) ns hf).trans
      (((Structural.substEmbedded x m b hn).restrictNames ns).trans
        (Structural.par_restrictNames_right (.embed (.active x m)) (.embed (b.substFree x m)) ns hf).symm))

/-- Unique active definitions supply the provider-domain side condition of
capture-avoiding substitution into an arbitrary current Named context. -/
theorem Structural.substNamed_fresh_of_unique (x : V) (m : Term V) (a : Named V)
    (hu : (Named.par (.embed (.active x m)) a).UniqueDefinitions) :
    ∃ (ns : List SourceName) (b : Extended V),
      Structural a (Named.restrictNames ns (.embed b)) ∧ ¬ b.Exports x ∧
      (∀ n ∈ ns, n ∉ (Extended.active x m).nameSupport) ∧
      Structural (.par (.embed (.active x m)) a)
        (.par (.embed (.active x m)) (Named.restrictNames ns (.embed (b.substFree x m)))) :=
  Structural.substNamed_fresh x m a (fun h => hu.2.2 x ⟨rfl,h⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
