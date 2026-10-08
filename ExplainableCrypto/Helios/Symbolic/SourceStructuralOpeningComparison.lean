import ExplainableCrypto.Helios.Symbolic.SourceOpeningVariableComparison

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type}

/-- Every original structural derivation transports any chosen fresh opening
in both directions. The resulting bodies have an actual binder-structural comparison;
allocation remains distinct and avoids the entire supplied finite set. -/
theorem Structural.openingEquivalent {a b : Named V} (h : Structural a b) :
    OpeningEquivalent a b := by
  induction h with
  | refl => exact .refl _
  | symm h ih => exact ih.symm
  | trans h j ih ij => exact ih.trans ij
  | embed h => exact openingEquivalent_embed h
  | parLeft c h ih => exact ⟨ih.1.parLeft c,ih.2.parLeft c⟩
  | parRight c h ih => exact ⟨ih.1.parRight c,ih.2.parRight c⟩
  | newName n h ih => exact ⟨ih.1.newName n,ih.2.newName n⟩
  | newVar h ih => exact ⟨ih.1.newVar,ih.2.newVar⟩
  | embedPar a b => exact openingEquivalent_embedPar a b
  | embedVar a => exact openingEquivalent_embedVar a
  | zero a => exact openingEquivalent_zero a
  | assoc a b c => exact openingEquivalent_assoc a b c
  | comm a b => exact openingEquivalent_comm a b
  | nameZero n => exact openingEquivalent_nameZero n
  | nameComm n m a => exact openingEquivalent_nameComm n m a
  | nameVarComm n a => exact openingEquivalent_nameVarComm n a
  | varComm a => exact openingEquivalent_varComm a
  | namePar a n b hf => exact openingEquivalent_namePar a b n hf
  | varPar a b => exact openingEquivalent_varPar a b
  | alphaBase a n m hf => exact openingEquivalent_alphaBase a n m hf
  | alphaChannel a n m hf => exact openingEquivalent_alphaChannel a n m hf

theorem Structural.transport_binder_opening {a b : Named V} (h : Structural a b)
    (ρ : NameAssignment) (ns : List SourceName) (p : Extended V) (avoid : Finset SourceName)
    (hp : Opens a ρ ns p) (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ ms q, Opens b ρ ms q ∧ (∀ m ∈ ms, m ∉ avoid) ∧ p.BinderStructural q :=
  h.openingEquivalent.1 ρ ns p avoid hp hf

/-- The existing semantic transport interface follows from the stronger
structural body witness, so clients retain full realization-class equality. -/
theorem Structural.transport_opening {a b : Named V} (h : Structural a b)
    (ρ : NameAssignment) (ns : List SourceName) (p : Extended V) (avoid : Finset SourceName)
    (hp : Opens a ρ ns p) (hf : ∀ n ∈ ns, n ∉ avoid) :
    ∃ ms q, Opens b ρ ms q ∧ (∀ m ∈ ms, m ∉ avoid) ∧ p.SameRealizations q := by
  obtain ⟨ms,q,hq,hg,he⟩ := h.transport_binder_opening ρ ns p avoid hp hf
  exact ⟨ms,q,hq,hg,he.sameRealizations⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
