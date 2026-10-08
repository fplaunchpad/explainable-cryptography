import ExplainableCrypto.Helios.Symbolic.SourceBackwardVisibleRealization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- An existing-handle output preserves the full old frame and domain. Only
continuations of outputs equal to that handle need be deterministic. -/
theorem FreeStep.output_sameRealizations_target {a b : Extended (Fin handles)}
    {c : Nat} {x : Fin handles} (h : FreeStep a (.output c x) b)
    (φ : Frame restricted handles) (p q : Agent Empty)
    (ha : a.SameRealizations (frameProcess φ p))
    (hd : ∀ m s, EqE (φ.value x) m → Agent.Visible p (.output c m) s → Agent.EvalEq s q) :
    b.SameRealizations (frameProcess φ q) := by
  intro env t
  rw [frameProcess_realizes_iff]
  constructor
  · intro hb
    obtain ⟨u,s,hu,hs,he⟩ := h.realizes_backward env hb
    obtain ⟨hv,hp⟩ := (frameProcess_realizes_iff φ p env u).mp ((ha env u).mp hu)
    obtain ⟨v,⟨m,hm,hmv⟩,hj⟩ := hs.transport hp.symm
    exact ⟨hv,(hd m v ((hv x).symm.trans hm) hmv).symm.trans (hj.symm.trans he)⟩
  · rintro ⟨hv,ht⟩
    have hp : a.Realizes env p := (ha env p).mpr
      ((frameProcess_realizes_iff φ p env p).mpr ⟨hv,.refl _⟩)
    obtain ⟨m,s,hm,hs,hb⟩ := h.output_realizes env hp
    exact hb.congr ((hd m s ((hv x).symm.trans hm) hs).trans ht)

/-- The full emitted message equals the value of the labelled old handle. -/
theorem FreeStep.output_of_sameRealizations {a b : Extended (Fin handles)}
    {c : Nat} {x : Fin handles} (h : FreeStep a (.output c x) b)
    (φ : Frame restricted handles) (p : Agent Empty)
    (ha : a.SameRealizations (frameProcess φ p)) :
    ∃ m q, EqE (φ.value x) m ∧ Agent.Visible p (.output c m) q ∧ b.Realizes φ.value q :=
  h.output_realizes φ.value ((ha _ _).mpr (frameProcess_realizes φ p))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
