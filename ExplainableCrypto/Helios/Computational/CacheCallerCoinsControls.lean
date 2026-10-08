import ExplainableCrypto.Helios.Computational.CacheCallerCoins

/-! Literal adaptive callers; results and remaining coins are independently fixed. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerCoinsControls
open OracleComp OracleSpec CacheCallerCoins BallotCacheCodecControls

private def handler : QueryImpl coinSpec (StateT (List Bool) Id) :=
  fun _ answers => (answers.headD false,answers.tail)

def adaptive : BallotOracleComp (ZMod 11) (PrimeGroup 23 11) (Nat × Nat × Nat × Nat) := do
  let u : Fin 2 ← liftM ((BallotOracleSpec (ZMod 11) (PrimeGroup 23 11)).query (.inl 1))
  let first := if u.val = 0 then key else otherKey
  let a : ZMod 11 ← liftM ((BallotOracleSpec (ZMod 11) (PrimeGroup 23 11)).query (.inr first))
  let b : ZMod 11 ← liftM ((BallotOracleSpec (ZMod 11) (PrimeGroup 23 11)).query (.inr first))
  let last := if a = 6 then otherKey else key
  let c : ZMod 11 ← liftM ((BallotOracleSpec (ZMod 11) (PrimeGroup 23 11)).query (.inr last))
  pure (u.val,a.val,b.val,c.val)

private def observe (state : CacheHashCoins.State 23 11) (answers : List Bool) :=
  (simulateQ handler (run 0 adaptive ((ballotCacheBitCodec 23 11).encode state.1)
    (CacheHashHandler.logEncode state.2))).run answers

/-- Uniform zero chooses key; six chooses the other last key. Repeat is a hit.
The old miss log is retained even when its key is initially absent from the cache. -/
theorem adaptive_control :
    observe (∅,[((),otherKey)])
      [false,true,false,true,true,false,true,false,false,false,true,false] =
      (some ((0,6,6,1),
        (ballotCacheBitCodec 23 11).encode ((AList.singleton key 6).insert otherKey 1),
        CacheHashHandler.logEncode [((),otherKey),((),key),((),otherKey)]),[true,false]) := by
  unfold observe
  rw [run_eq]
  rfl

/-- A different first uniform answer selects the other cached key. All three
hashes hit, and only the first two uniform-sampling coins are consumed. -/
theorem hits_control :
    observe (cache,[((),key)]) [true,false,false,true,true,false] =
      (some ((1,5,5,3),(ballotCacheBitCodec 23 11).encode cache,
        CacheHashHandler.logEncode [((),key)]),[false,true,true,false]) := by
  unfold observe
  rw [run_eq]
  rfl

/-- Unit range still consumes its specified one coin and returns zero. -/
theorem unit_control :
    (simulateQ handler (sampleIndex 1 0)).run [true,false] = (some 0,[false]) := by
  rw [sampleIndex_eq]
  rfl

/-- The actual cache-preserving repeat cannot produce a different second answer. -/
theorem repeat_not_changed :
    (observe (∅,[((),otherKey)])
      [false,true,false,true,true,false,true,false,false,false,true,false]).1.map
        (fun out => out.1.2.2.1) ≠ some 1 := by
  rw [adaptive_control]
  decide

private theorem adaptive_bound : adaptive.IsTotalQueryBound 4 := by
  unfold adaptive
  simp only [isTotalQueryBound_query_bind_iff]
  exact ⟨by decide,fun _ => ⟨by decide,fun _ => ⟨by decide,fun _ =>
    ⟨by decide,fun _ => trivial⟩⟩⟩⟩

/-- Full-state error follows from the source caller's budget, with no separate
exact-source budget or correspondence supplied as a premise. -/
theorem distance_control :
    SPMF.tvDist
      (evalSPMF (run 3 adaptive ((ballotCacheBitCodec 23 11).encode ∅)
        (CacheHashHandler.logEncode [((),otherKey)])))
      (evalSPMF ((fun out => some (encode out)) <$> source adaptive (∅,[((),otherKey)]))) ≤
        (2 : ℝ)⁻¹ := by
  have h := distance 3 adaptive (∅,[((),otherKey)]) 4 adaptive_bound
  norm_num at h ⊢
  exact h

end ExplainableCrypto.Helios.Computational.CacheCallerCoinsControls
