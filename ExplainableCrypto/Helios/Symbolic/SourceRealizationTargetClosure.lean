import ExplainableCrypto.Helios.Symbolic.SourceBackwardRealization

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

theorem SameRealizations.mapNames {a b : Extended V} (h : SameRealizations a b)
    (e k : Nat ≃ Nat) : SameRealizations (a.mapNames e k) (b.mapNames e k) := by
  intro env p
  rw [realizes_mapped_environment_iff,realizes_mapped_environment_iff]
  exact h _ _

/-- If the full source realizations are exactly a canonical frame/body and all
canonical internal outcomes agree, the full target realizations are exactly
that frame and the chosen successor body. Determinism is an explicit premise;
this is stronger than one existential interpretation in the frame environment. -/
theorem Reduction.sameRealizations_frame_target {a b : Extended (Fin handles)}
    (h : Reduction a b) (φ : Frame restricted handles) (p q : Agent Empty)
    (ha : a.SameRealizations (frameProcess φ p))
    (hd : ∀ r, Agent.Tau p r → Agent.EvalEq r q) :
    b.SameRealizations (frameProcess φ q) := by
  intro env t
  rw [frameProcess_realizes_iff]
  constructor
  · intro hb
    obtain ⟨u,r,hu,hr,he⟩ := h.realizes_backward env hb
    obtain ⟨hv,hp⟩ := (frameProcess_realizes_iff φ p env u).mp ((ha env u).mp hu)
    obtain ⟨s,hs,hj⟩ := hp.symm.tau_transport hr
    exact ⟨hv,(hd s hs).symm.trans (hj.symm.trans he)⟩
  · rintro ⟨hv,ht⟩
    have hp : a.Realizes env p := (ha env p).mpr
      ((frameProcess_realizes_iff φ p env p).mpr ⟨hv,.refl _⟩)
    obtain ⟨r,hr,hb⟩ := h.realizes env hp
    exact hb.congr ((hd r hr).trans ht)

/-- A canonical full-realization invariant rules out a source reduction when
the canonical body has no actual internal step. -/
theorem no_reduction_of_sameRealizations_quiet {a b : Extended (Fin handles)}
    (φ : Frame restricted handles) (p : Agent Empty)
    (ha : a.SameRealizations (frameProcess φ p)) (hq : ∀ q, ¬ Agent.Tau p q) :
    ¬ Reduction a b := by
  intro h
  obtain ⟨q,ht,_⟩ := h.realizes φ.value ((ha φ.value p).mpr (frameProcess_realizes φ p))
  exact hq q ht

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
