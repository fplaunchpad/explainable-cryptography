import ExplainableCrypto.Helios.Computational.CacheHashCoins

/-! Independent literal cache answers, chronological miss logs and unused coins. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashCoinsControls
open OracleComp OracleSpec CacheHashCoins BallotCacheCodecControls

private def handler : QueryImpl coinSpec (StateT (List Bool) Id) :=
  fun _ answers => (answers.headD false,answers.tail)

private def observe (width : List Bool) (state : State 23 11) (answers : List Bool) :=
  (simulateQ handler (hash 23 11 width ((ballotKeyBitCodec 23 11).encode key)
    ((ballotCacheBitCodec 23 11).encode state.1) (CacheHashHandler.logEncode state.2))).run answers

/-- Stored scalar three has prefix 11011, and the old cache/log are untouched. -/
theorem hit_control :
    hash 23 11 [true,true,true,true] ((ballotKeyBitCodec 23 11).encode key)
      ((ballotCacheBitCodec 23 11).encode cache) (CacheHashHandler.logEncode [((),otherKey)]) =
      pure (some ([true,true,false,true,true],(ballotCacheBitCodec 23 11).encode cache,
        CacheHashHandler.logEncode [((),otherKey)])) := by
  exact hash_hit _ key (cache,[((),otherKey)]) 3 (by decide)

/-- Four literal coins 0110 produce six; insert its original prefix and append the key. -/
theorem miss_control :
    observe [true,true,true,true] (∅,[((),otherKey)]) [false,true,true,false,true,false] =
      (some ([true,true,true,false,false,true,true],
        (ballotCacheBitCodec 23 11).encode (AList.singleton key 6),
        CacheHashHandler.logEncode [((),otherKey),((),key)]),[true,false]) := by
  unfold observe
  rw [hash_miss _ key (∅,[((),otherKey)]) (by rfl)]
  rfl

/-- Empty width samples zero without querying and still inserts its delimiter. -/
theorem zero_control :
    observe [] (∅,[]) [true,false] =
      (some ([false],(ballotCacheBitCodec 23 11).encode (AList.singleton key 0),
        CacheHashHandler.logEncode [((),key)]),[true,false]) := by
  unfold observe
  rw [hash_miss _ key (∅,[]) (by rfl)]
  rfl

/-- A hit cannot silently become an eager coin-querying branch. -/
theorem hit_not_resampled (next : Bool → OracleComp coinSpec (Option Output)) :
    hash 23 11 [true,true,true,true] ((ballotKeyBitCodec 23 11).encode key)
      ((ballotCacheBitCodec 23 11).encode cache) (CacheHashHandler.logEncode [((),otherKey)]) ≠
        (coin >>= next) := by
  rw [hit_control]
  intro h
  have hp := congrArg OracleComp.isPure h
  simp [coin,OracleComp.isPure_query_bind,OracleComp.isPure_pure] at hp

/-- The concrete full-output error is bounded, with an actual nonempty cache/log. -/
theorem distance_control :
    SPMF.tvDist
      (evalSPMF (hash 23 11 (List.replicate 7 true) ((ballotKeyBitCodec 23 11).encode key)
        ((ballotCacheBitCodec 23 11).encode (AList.singleton otherKey 5))
        (CacheHashHandler.logEncode [((),otherKey)])))
      (evalSPMF (ideal key (AList.singleton otherKey 5,[((),otherKey)]))) ≤ (8 : ℝ)⁻¹ := by
  rw [hash_source]
  simpa only [show Nat.size 11+3 = 7 by decide, show (2:ℝ)^3 = 8 by norm_num] using
    hash_distance 3 key (AList.singleton otherKey 5,[((),otherKey)])

end ExplainableCrypto.Helios.Computational.CacheHashCoinsControls
