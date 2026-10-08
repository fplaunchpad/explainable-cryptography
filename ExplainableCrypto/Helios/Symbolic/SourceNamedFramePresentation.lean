import ExplainableCrypto.Helios.Symbolic.SourceAdmissiblePrenex

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- A complete ground active frame under explicit sorted name restrictions. -/
noncomputable def canonicalFrame (hidden : Finset Nat) (φ : Frame restricted handles) : Named (Fin handles) :=
  restrictNames (restrictionNames hidden restricted) (.embed (Extended.activeFrame φ))

/-- A source structural witness for the restricted substitution presentation
used in Definition 1. The complete original frameOf is on the left. -/
def RepresentsFrame (a : Named (Fin handles)) (hidden : Finset Nat) (φ : Frame restricted handles) : Prop :=
  Structural a.frameOf (canonicalFrame hidden φ)

theorem canonicalFrame_frameOf (φ : Frame restricted handles) :
    (canonicalFrame hidden φ).frameOf = canonicalFrame hidden φ := by
  simp only [canonicalFrame,frameOf_restrictNames,frameOf,Extended.activeFrame_frameOf]

theorem canonicalFrame_represents (φ : Frame restricted handles) :
    (canonicalFrame hidden φ).RepresentsFrame hidden φ := by
  unfold RepresentsFrame
  rw [canonicalFrame_frameOf]
  exact .refl _

theorem restrictedState_represents (p : ScopedState restricted handles) :
    (restrictedState hidden p).RepresentsFrame hidden p.frame := restrictedState_frameOf hidden p

theorem RepresentsFrame.structural {a b : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) (hab : Structural a b) : b.RepresentsFrame hidden φ :=
  hab.frameOf.symm.trans h

theorem RepresentsFrame.internal {a b : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) (hab : Reduction a b) : b.RepresentsFrame hidden φ :=
  hab.frameOf.symm.trans h

theorem RepresentsFrame.free {a b : Named (Fin handles)} {φ : Frame restricted handles}
    {l : Extended.FreeLabel (Fin handles)} (h : a.RepresentsFrame hidden φ) (hab : FreeStep a l b) :
    b.RepresentsFrame hidden φ := hab.frameOf.symm.trans h

theorem RepresentsFrame.all_exports {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) : ∀ v, a.Exports v := by
  intro v
  exact (a.frameOf_exports v).mp ((h.exports v).mpr
    ((restrictNames_exports _ _ v).mpr (Extended.activeFrame_exports φ v)))

theorem RepresentsFrame.wellFormed {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) : a.WellFormed := by
  refine ⟨a.frameOf_uniqueDefinitions.mp (h.uniqueDefinitions.mpr ?_),closed_of_all_exports a h.all_exports⟩
  exact (restrictNames_uniqueDefinitions _ _).mpr (Extended.activeFrame_wellFormed φ).1

/-- Hiding the new output handle recovers this same presented frame. The
unrestricted target has an additional public handle and is not equated here. -/
theorem RepresentsFrame.bound_reclose {a : Named (Fin handles)} {b : Named (Option (Fin handles))}
    {c : Nat} {φ : Frame restricted handles} (h : a.RepresentsFrame hidden φ) (hab : BoundOutput a c b) :
    (Named.newVar b).RepresentsFrame hidden φ := hab.frameOf_reclose.trans h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
