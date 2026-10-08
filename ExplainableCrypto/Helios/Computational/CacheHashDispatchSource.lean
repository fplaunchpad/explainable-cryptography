import ExplainableCrypto.Helios.Computational.CacheHashDispatchRun
import ExplainableCrypto.Helios.Computational.CacheHashCoins

/-! The complete finite dispatcher refines the existing adaptive caller's cache
request specification. The caller's own loading and continuations remain separate. -/
namespace ExplainableCrypto.Helios.Computational.CacheHashDispatch
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [NeZero p] [NeZero q]

/-- The full dispatcher returns precisely the existing request's encoded scalar,
cache and chronological log as a raw coin-query tree. -/
theorem readout_source (key : BallotForkPoint (PrimeGroup p q))
    (state : CacheHashCoins.State p q) (slack : Nat) :
    readout <$> request state.1 key state.2 slack =
      simulateQ CoinWordLoader.liftCoins (CacheHashCoins.hashPrepared p q slack
        ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
        (CacheHashHandler.logEncode state.2)) := by
  rw [CacheHashCoins.hashPrepared_eq]
  cases found : state.1.lookup key with
  | some value =>
    rw [CacheHashCoins.hash_hit _ key state value found]
    simp [request,found,readout,result,CacheHashCoins.encode,CacheHashHandler.logEncode]
  | none =>
    rw [CacheHashCoins.hash_miss _ key state found]
    simp only [List.length_replicate,request,found,Functor.map_map,simulateQ_map]
    let f : Nat → Option CacheHashCoins.Output := fun n => some (CacheHashCoins.encode
      ((n : ZMod q),state.1.insert key (n : ZMod q),state.2++[((),key)]))
    have hi := congrArg (fun oa : OracleComp spec Nat => f <$> oa)
      (CoinWordLoader.word_index (q.size+slack))
    simp only [simulateQ_map,Functor.map_map] at hi
    have hleft : (fun bits => readout (sampledResult state.1 key state.2
        (SamplerOperands.input slack q []) bits)) = (fun bits => f (bitsValue bits)) := by
      funext bits
      simp [sampledResult,readout,result,f,CacheHashCoins.encode,CacheHashHandler.logEncode]
    rw [hleft,hi]
    simp only [sampleFairBitModulo,simulateQ_map,Functor.map_map]
    congr 1
    funext a
    have hv : (ZMod.finEquiv q) ⟨a.val % q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩ =
        (a.val : ZMod q) := by
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q => rfl
    rw [hv]

/-- Direct correspondence from actual finite execution to the existing cache
caller interface; every workspace and charge premise is discharged above. -/
theorem execution_source (key : BallotForkPoint (PrimeGroup p q))
    (state : CacheHashCoins.State p q) (slack : Nat) :
    (fun out => readout out.1) <$>
      run code (requestClock state.1 key state.2 slack)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
          (CacheHashHandler.logEncode state.2) (SamplerOperands.input slack q [])) =
      simulateQ CoinWordLoader.liftCoins (CacheHashCoins.hashPrepared p q slack
        ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
        (CacheHashHandler.logEncode state.2)) := by
  have he := congrArg (fun oa => readout <$> oa) (request_run state.1 key state.2 slack).1
  simp only [Functor.map_map] at he
  exact he.trans (readout_source key state slack)

end ExplainableCrypto.Helios.Computational.CacheHashDispatch
