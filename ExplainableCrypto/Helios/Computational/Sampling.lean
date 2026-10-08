import ExplainableCrypto.Helios.Computational.BallotProof
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! Smyth's nonzero encryption-nonce distribution, separate from arbitrary
adversarial ciphertexts. The generic VCVio encryption samples all scalars. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp

variable {F G : Type} [Field F] [Fintype F] [AddCommGroup G] [Module F G]

noncomputable def sampleNonzero (F : Type) [Field F] [Fintype F] : ProbComp F := by
  classical
  letI : SampleableType Fˣ := SampleableType.ofFintype Fˣ
  exact Units.val <$> uniformSample Fˣ

theorem sampleNonzero_ne_zero {r : F} (hr : r ∈ support (sampleNonzero F)) : r ≠ 0 := by
  simp only [sampleNonzero, support_map] at hr
  obtain ⟨u, _, rfl⟩ := hr
  exact Units.ne_zero u

theorem sampleNonzero_probability (u : Fˣ) :
    Pr[= (u : F) | sampleNonzero F] = ((Fintype.card F - 1 : Nat) : ENNReal)⁻¹ := by
  classical
  let : SampleableType Fˣ := SampleableType.ofFintype Fˣ
  change Pr[= (u : F) | Units.val <$> uniformSample Fˣ] = _
  rw [probOutput_map_injective _ Units.val_injective]
  simp [Fintype.card_units]

noncomputable def honestEncrypt (g pk : G) (m : F) : ProbComp (Ciphertext G) := do
  let r ← sampleNonzero F
  pure (encryptWith g pk r m)

/-- Honest encryption cannot produce the neutral ciphertext when generator
exponentiation is injective. This follows from its actual sampling support. -/
theorem honestEncrypt_ne_neutral (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (m : F)
    {ct : Ciphertext G} (hc : ct ∈ support (honestEncrypt g pk m)) :
    ct ≠ (0, 0) := by
  simp only [honestEncrypt, support_bind, support_pure, Set.mem_iUnion,
    Set.mem_singleton_iff] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  intro h
  have hzero : r • g = (0 : F) • g := by
    simpa [encryptWith] using congrArg Prod.fst h
  exact sampleNonzero_ne_zero hr (hg hzero)

#print axioms encryptWith_vcvio
#print axioms sampleNonzero_ne_zero
#print axioms sampleNonzero_probability
#print axioms honestEncrypt_ne_neutral

end ExplainableCrypto.Helios.Computational
