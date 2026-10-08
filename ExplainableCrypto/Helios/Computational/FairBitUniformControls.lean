import ExplainableCrypto.Helios.Computational.FairBitUniformOracle

/-! A real two-query source whose second range depends on its first answer. -/
namespace ExplainableCrypto.Helios.Computational.FairBitUniformControls
open OracleComp OracleSpec

def adaptiveRanges : ProbComp (Nat × Nat) := do
  let x ← liftM (unifSpec.query 2)
  let y ← liftM (unifSpec.query (x.val+1))
  pure (x.val,y.val)

private theorem adaptive_bound : adaptiveRanges.IsTotalQueryBound 2 := by
  exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩

/-- The complete pair, retaining the first answer, meets the two-request bound. -/
theorem adaptive_distance (slack : Nat) :
    SPMF.tvDist (evalSPMF (runFairBitUniform slack adaptiveRanges))
      (evalSPMF adaptiveRanges) ≤ 2*((2 : ℝ)^slack)⁻¹ := by
  simpa only [Nat.cast_ofNat] using runFairBitUniform_tv_le slack adaptiveRanges 2 adaptive_bound

/-- An adaptive answer must stay inside the range selected by its actual prefix. -/
theorem adaptive_range_preserved (slack : Nat) (out : Nat × Nat)
    (ho : out ∈ support (runFairBitUniform slack adaptiveRanges)) :
    out.1 < 3 ∧ out.2 < out.1+2 := by
  have h := runFairBitUniform_support_subset slack adaptiveRanges ho
  simp only [adaptiveRanges,support_bind,support_pure,Set.mem_iUnion,exists_prop,
    Set.mem_singleton_iff] at h
  obtain ⟨x,_,y,_,rfl⟩ := h
  exact ⟨x.isLt,y.isLt⟩

#print axioms adaptive_distance
#print axioms adaptive_range_preserved
end ExplainableCrypto.Helios.Computational.FairBitUniformControls
