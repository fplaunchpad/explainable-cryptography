import ExplainableCrypto.Helios.Computational.PrimeSamplers

/-! Literal nonzero coverage and a joint-distribution control against nonce reuse. -/
namespace ExplainableCrypto.Helios.Computational.PrimeSamplersControls
open OracleComp OracleSpec
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Explicit indices cover every nonzero residue once, including the endpoint. -/
theorem literal_enumeration :
    (List.finRange 4).map (primeNonceValue (q := 5)) = [1,2,3,4] ∧
    (primeNonceEquiv (q := 5)).symm (1 : (ZMod 5)ˣ) = 0 := by decide

private theorem one_probability :
    Pr[= (1 : ZMod 5) | samplePrimeNonzero] = (4 : ENNReal)⁻¹ := by
  rw [samplePrimeNonzero_probability]
  have h := sampleNonzero_probability (1 : (ZMod 5)ˣ)
  simpa using h

private theorem two_probability :
    Pr[= (2 : ZMod 5) | samplePrimeNonzero] = (4 : ENNReal)⁻¹ := by
  rw [samplePrimeNonzero_probability]
  have h := sampleNonzero_probability (Units.mk0 (2 : ZMod 5) (by decide))
  simpa using h

/-- Independent nonces can differ; each ordered pair has its product mass. -/
theorem independent_pair : Pr[= ((1 : ZMod 5),2) | drawPrimeNoncePair] =
    (16 : ENNReal)⁻¹ := by
  simp [drawPrimeNoncePair,one_probability,two_probability]
  rw [← ENNReal.mul_inv] <;> norm_num

def reusedNonce : ProbComp (ZMod 5 × ZMod 5) := do
  let r ← samplePrimeNonzero
  pure (r,r)

/-- Reusing a uniform nonce has the wrong joint distribution, despite uniform marginals. -/
theorem reused_pair_rejected : Pr[= ((1 : ZMod 5),2) | reusedNonce] = 0 := by
  apply probOutput_eq_zero_of_not_mem_support
  simp only [reusedNonce,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  rintro ⟨r,_,h⟩
  have h12 : (1 : ZMod 5) = 2 := (congrArg Prod.fst h).trans (congrArg Prod.snd h).symm
  exact (by decide : (1 : ZMod 5) ≠ 2) h12

/-- Zero is absent from the actual explicit sampler's support. -/
theorem zero_rejected : Pr[= (0 : ZMod 5) | samplePrimeNonzero] = 0 := by
  rw [samplePrimeNonzero_probability]
  exact probOutput_eq_zero_of_not_mem_support (fun h => sampleNonzero_ne_zero h rfl)

#print axioms literal_enumeration
#print axioms independent_pair
#print axioms reused_pair_rejected
#print axioms zero_rejected
end ExplainableCrypto.Helios.Computational.PrimeSamplersControls
