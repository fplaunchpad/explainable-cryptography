import ExplainableCrypto.Helios.Symbolic.SourceLocalNormalization
import ExplainableCrypto.Helios.Symbolic.SourceNamedGeneralSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Expose a fresh name prefix, eliminate the variable under that prefix, and
retain the actual instantiated body. Freshness prevents an external name in
the provider from being captured by a formerly private context binder. -/
theorem let_normalize_fresh (m : Term V) (a : Named (Option V)) (ha : ¬ a.Exports none) :
    ∃ (ns : List SourceName) (b : Extended (Option V)) (c : Extended V),
      Structural a (Named.restrictNames ns (.embed b)) ∧
      (∀ n ∈ ns, n ∉ (Extended.active none (shiftTerm m)).nameSupport) ∧
      ¬ b.Exports none ∧ Extended.Instantiates (inputSubst m) b c ∧
      Structural (.newVar (.par (.embed (.active none (shiftTerm m))) a))
        (Named.restrictNames ns (.embed c)) := by
  obtain ⟨ns,b,hb,hf⟩ := exists_fresh_prenex a (Extended.active none (shiftTerm m)).nameSupport
  have hn : ¬ b.Exports none := fun h => ha
    ((hb.exports none).mpr ((restrictNames_exports ns _ none).mpr h))
  obtain ⟨c,hc,hs⟩ := Extended.let_normalize_exists m b hn
  refine ⟨ns,b,c,hb,hf,hn,hc,?_⟩
  have hp := (Structural.parRight (.embed (.active none (shiftTerm m))) hb).trans
    (Structural.par_restrictNames_right (.embed (.active none (shiftTerm m))) (.embed b) ns hf)
  have he : Structural (.newVar (.par (.embed (.active none (shiftTerm m))) (.embed b))) (.embed c) :=
    (Structural.newVar (Structural.embedPar _ _).symm).trans
      ((Structural.embedVar _).symm.trans (Structural.embed hs))
  exact (Structural.newVar hp).trans ((Structural.var_restrictNames _ ns).trans (he.restrictNames ns))

/-- Unique definitions discharge the side condition in the full Named context. -/
theorem let_normalize_fresh_of_unique (m : Term V) (a : Named (Option V))
    (hu : (Named.newVar (.par (.embed (.active none (shiftTerm m))) a)).UniqueDefinitions) :
    ∃ (ns : List SourceName) (b : Extended (Option V)) (c : Extended V),
      Structural a (Named.restrictNames ns (.embed b)) ∧
      (∀ n ∈ ns, n ∉ (Extended.active none (shiftTerm m)).nameSupport) ∧
      ¬ b.Exports none ∧ Extended.Instantiates (inputSubst m) b c ∧
      Structural (.newVar (.par (.embed (.active none (shiftTerm m))) a))
        (Named.restrictNames ns (.embed c)) :=
  let_normalize_fresh m a (fun h => hu.1.2.2 none ⟨rfl,h⟩)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
