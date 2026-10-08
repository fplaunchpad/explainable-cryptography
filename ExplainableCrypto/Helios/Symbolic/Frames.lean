import ExplainableCrypto.Helios.Symbolic.Equations

namespace ExplainableCrypto.Helios.Symbolic

/-- Both compared worlds reserve the same names and expose the same handle domain.
This fits the historical swapped-vote frames; alpha-renaming is a separate layer. -/
structure Frame (restricted : Finset Nat) (n : Nat) where
  value : Fin n → Ground

namespace Frame
variable {restricted : Finset Nat} {n m : Nat}

def eval (φ : Frame restricted n) (r : Recipe n) : Ground := r.subst φ.value

/-- Static equivalence tests all public recipes, not syntactic equality of frames. -/
def StaticEq (φ ψ : Frame restricted n) : Prop :=
  ∀ r s : Recipe n, r.Public restricted → s.Public restricted →
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s))

theorem StaticEq.refl (φ : Frame restricted n) : StaticEq φ φ := by
  intro _ _ _ _
  rfl

theorem StaticEq.symm {φ ψ : Frame restricted n} (h : StaticEq φ ψ) : StaticEq ψ φ := by
  intro r s hr hs
  exact (h r s hr hs).symm

theorem StaticEq.trans {φ ψ χ : Frame restricted n}
    (h : StaticEq φ ψ) (h' : StaticEq ψ χ) : StaticEq φ χ := by
  intro r s hr hs
  exact (h r s hr hs).trans (h' r s hr hs)

/-- Sufficient for equationally identical frames; not a privacy proof for ciphertexts
with different hidden plaintexts. -/
theorem staticEq_of_pointwise {φ ψ : Frame restricted n}
    (h : ∀ i, EqE (φ.value i) (ψ.value i)) : StaticEq φ ψ := by
  intro r s _ _
  have hr := r.subst_congr φ.value ψ.value h
  have hs := s.subst_congr φ.value ψ.value h
  exact ⟨fun he => hr.symm.trans (he.trans hs),
    fun he => hr.trans (he.trans hs.symm)⟩

/-- Public computation can select, combine, or duplicate any exposed handles. -/
def derive (φ : Frame restricted n) (recipes : Fin m → Recipe n) : Frame restricted m :=
  ⟨fun i => φ.eval (recipes i)⟩

end Frame

/-- Substituting public recipes does not introduce a restricted name. -/
theorem Term.Public.subst {V W : Type} {restricted : Finset Nat}
    (r : Term V) (σ : V → Term W) (hr : r.Public restricted)
    (hσ : ∀ v, (σ v).Public restricted) : (r.subst σ).Public restricted := by
  induction r with
  | name => exact hr
  | var v => exact hσ v
  | const => trivial
  | unary f a ih => exact ih hr
  | binary f a b ih₁ ih₂ => exact ⟨ih₁ hr.1, ih₂ hr.2⟩
  | ternary f a b c ih₁ ih₂ ih₃ => exact ⟨ih₁ hr.1, ih₂ hr.2.1, ih₃ hr.2.2⟩
  | spk a b c d ih₁ ih₂ ih₃ ih₄ =>
      exact ⟨ih₁ hr.1, ih₂ hr.2.1, ih₃ hr.2.2.1, ih₄ hr.2.2.2⟩

/-- Arbitrary public recipe postprocessing preserves static equivalence. -/
theorem Frame.StaticEq.derive {restricted : Finset Nat} {n m : Nat}
    {φ ψ : Frame restricted n} (h : φ.StaticEq ψ) (ρ : Fin m → Recipe n)
    (hρ : ∀ i, (ρ i).Public restricted) : (φ.derive ρ).StaticEq (ψ.derive ρ) := by
  intro r s hr hs
  have he := h (r.subst ρ) (s.subst ρ) (Term.Public.subst r ρ hr hρ) (Term.Public.subst s ρ hs hρ)
  simpa only [Frame.eval, Frame.derive, Term.subst_subst] using he

end ExplainableCrypto.Helios.Symbolic
