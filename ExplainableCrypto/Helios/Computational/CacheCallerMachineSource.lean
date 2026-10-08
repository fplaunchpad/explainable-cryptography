import ExplainableCrypto.Helios.Computational.CacheCallerMachineRun
import ExplainableCrypto.Helios.Computational.CacheRequestPrefixBounds

/-! Connect resident entry/return to the existing request specification, source
budget bounds and physical compiler. Enclosing source operand production and
continuation execution remain explicit obligations. -/
namespace ExplainableCrypto.Helios.Computational.CacheCallerMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [NeZero p] [NeZero q]
attribute [local irreducible] code clock cost CacheHashDispatch.code

def readout (cfg : Config 13 size 3) : Option (List Bool × List Bool × List Bool) :=
  if cfg.l = none ∧ cfg.var = 2 then some (cfg.stk 7,cfg.stk 9,cfg.stk 10) else none

private theorem readout_result (cfg : Config 12 CacheHashDispatch.size 3) (saved : List Bool) :
    readout (result cfg saved) = CacheHashDispatch.readout cfg := by
  rcases cfg with ⟨label,v,words⟩
  cases label <;> fin_cases v <;> rfl

/-- The original host caller's complete hash-request observation is preserved
by actual resident entry, dispatch, return and saved-data framing. -/
theorem execution_source (key : BallotForkPoint (PrimeGroup p q))
    (state : CacheHashCoins.State p q) (slack : Nat) (previous saved : List Bool) :
    (fun out => readout out.1) <$>
      run code (clock state.1 key state.2 slack previous)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
          (CacheHashHandler.logEncode state.2) (SamplerOperands.input slack q []) previous saved) =
      simulateQ CoinWordLoader.liftCoins (CacheHashCoins.hashPrepared p q slack
        ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode state.1)
        (CacheHashHandler.logEncode state.2)) := by
  have h := congrArg (fun oa => readout <$> oa) (request_run state.1 key state.2 slack previous saved).1
  simp only [Functor.map_map,readout_result] at h
  exact h.trans (CacheHashDispatch.readout_source key state slack)

/-- Entry/return charge plus the existing dispatcher charge has a derived
linear bound in the combined local clock. -/
theorem cost_le_clock (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack : Nat) (previous : List Bool) :
    cost cache key log slack previous ≤ 32*clock cache key log slack previous := by
  have h := CacheHashDispatch.request_cost_le_clock cache key log slack
  unfold cost clock loadClock loadCost
  omega

/-- The previously derived source prestate bounds also bound resident entry.
The old answer length remains explicit until actual caller decoding/production
is connected; saved-data height belongs to the physical bound below. -/
theorem source_clock_bound {A : Type}
    (oa : BallotOracleComp (ZMod q) (PrimeGroup p q) A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (initial : BallotFiniteLoggedState (ZMod q) (PrimeGroup p q))
    (out : A × CacheRequestPrefixes.State (ZMod q) (PrimeGroup p q))
    (ho : out ∈ support (CacheRequestPrefixes.run oa initial))
    (e : CacheRequestPrefixes.Event (ZMod q) (PrimeGroup p q)) (he : e ∈ out.2.2)
    (key : BallotForkPoint (PrimeGroup p q)) (slack : Nat) (previous : List Bool) :
    clock e.2.1 key e.2.2 slack previous ≤
      previous.length+3*cacheRecordBitBound p q (initial.1.entries.length+n)+5+
        CacheRequestPrefixes.requestBound p q (initial.1.entries.length+n) (initial.2.length+n) slack := by
  have hs := (CacheRequestPrefixes.encoded_prestates_bound oa n hb initial out ho e he).1
  have hr := CacheRequestPrefixes.request_clock_bound oa n hb initial out ho e he key slack
  unfold CacheRequestMachine.clock at hr
  unfold clock loadClock
  omega

private theorem within_support (limit bound : Nat)
    (oa : OracleComp spec (Config 13 size 3 × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

/-- The compiler contract follows from actual resident execution, with no
externally supplied return, frame, termination or cost certificate. -/
theorem within (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat)
    (previous saved : List Bool) :
    BitOracleLoopBounded.Within limit (cost cache key log slack previous)
      (run code (clock cache key log slack previous)
        (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
          (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) previous saved)) :=
  within_support limit _ _ (request_run cache key log slack previous saved).2

/-- Actual primitive execution from the resident caller layout. Saved-word
height contributes to the physical time; this does not assume its width is
polynomial or that arbitrary host continuations have been compiled. -/
theorem physical_run (cache : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (key : BallotForkPoint (PrimeGroup p q))
    (log : List (Unit × BallotForkPoint (PrimeGroup p q))) (slack limit : Nat)
    (previous saved : List Bool) :
    let cfg := start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) previous saved
    let B := cost cache key log slack previous
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      (some ∘ fun cfg => result cfg saved) <$>
        simulateQ (BitOracleLoopBounded.adapter limit) (CacheHashDispatch.request cache key log slack) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock cache key log slack previous) limit
    (cost cache key log slack previous)
    (start ((ballotKeyBitCodec p q).encode key) ((ballotCacheBitCodec p q).encode cache)
      (((ballotLogEntryBitCodec p q).list).encode log) (SamplerOperands.input slack q []) previous saved)
    [] (OracleTapeOutput.wordTape []) (within cache key log slack limit previous saved)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (request_run cache key log slack previous saved).1
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms execution_source
#print axioms cost_le_clock
#print axioms source_clock_bound
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.CacheCallerMachine
