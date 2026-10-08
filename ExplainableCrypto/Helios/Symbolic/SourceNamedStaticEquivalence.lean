import ExplainableCrypto.Helios.Symbolic.SourceNamedFramePresentation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {handles : Nat}

/-- Definition 1's common restricted-substitution witness for complete finite
ground-presentable Named frames. Both structural paths and all-public-recipe
full-E equivalence are required. Existence of presentations is not assumed for
arbitrary raw syntax; the relation itself carries these witnesses. -/
def StaticEq (a b : Named (Fin handles)) : Prop :=
  ∃ (hidden restricted : Finset Nat) (φ ψ : Frame restricted handles),
    a.RepresentsFrame hidden φ ∧ b.RepresentsFrame hidden ψ ∧ φ.StaticEq ψ

variable {restricted hidden : Finset Nat} {a b a' b' : Named (Fin handles)}

theorem StaticEq.of_presentations {φ ψ : Frame restricted handles}
    (ha : a.RepresentsFrame hidden φ) (hb : b.RepresentsFrame hidden ψ) (he : φ.StaticEq ψ) :
    StaticEq a b := ⟨hidden,restricted,φ,ψ,ha,hb,he⟩

theorem RepresentsFrame.staticEq_self {φ : Frame restricted handles} (h : a.RepresentsFrame hidden φ) :
    StaticEq a a := .of_presentations h h (.refl φ)

theorem StaticEq.symm (h : StaticEq a b) : StaticEq b a := by
  obtain ⟨hidden,restricted,φ,ψ,ha,hb,he⟩ := h
  exact .of_presentations hb ha he.symm

theorem StaticEq.structural (h : StaticEq a b) (ha : Structural a a') (hb : Structural b b') :
    StaticEq a' b' := by
  obtain ⟨hidden,restricted,φ,ψ,hφ,hψ,he⟩ := h
  exact .of_presentations (hφ.structural ha) (hψ.structural hb) he

theorem staticEq_structural_iff (ha : Structural a a') (hb : Structural b b') :
    StaticEq a b ↔ StaticEq a' b' :=
  ⟨fun h => h.structural ha hb,fun h => h.structural ha.symm hb.symm⟩

theorem StaticEq.internal_left (h : StaticEq a b) (ha : Reduction a a') : StaticEq a' b := by
  obtain ⟨hidden,restricted,φ,ψ,hφ,hψ,he⟩ := h
  exact .of_presentations (hφ.internal ha) hψ he

theorem StaticEq.free_left (h : StaticEq a b) {l : Extended.FreeLabel (Fin handles)}
    (ha : FreeStep a l a') : StaticEq a' b := by
  obtain ⟨hidden,restricted,φ,ψ,hφ,hψ,he⟩ := h
  exact .of_presentations (hφ.free ha) hψ he

theorem StaticEq.complete_domains (h : StaticEq a b) : (∀ v, a.Exports v) ∧ (∀ v, b.Exports v) := by
  obtain ⟨_,_,_,_,ha,hb,_⟩ := h
  exact ⟨ha.all_exports,hb.all_exports⟩

theorem StaticEq.wellFormed (h : StaticEq a b) : a.WellFormed ∧ b.WellFormed := by
  obtain ⟨_,_,_,_,ha,hb,_⟩ := h
  exact ⟨ha.wellFormed,hb.wellFormed⟩

/-- Canonical restricted source states supply both actual presentation paths;
the checked full Frame.StaticEq supplies every public equality test. -/
theorem restrictedState_staticEq_of_frames (p q : ScopedState restricted handles) (h : p.frame.StaticEq q.frame) :
    StaticEq (restrictedState hidden p) (restrictedState hidden q) :=
  .of_presentations (restrictedState_represents p) (restrictedState_represents q) h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
