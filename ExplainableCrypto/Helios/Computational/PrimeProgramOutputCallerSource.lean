import ExplainableCrypto.Helios.Computational.PrimeProgramOutputCallerRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgramOutputCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
-- Keep proof-side unification from executing the concrete arithmetic clock.
-- Execution is rewritten only through the checked run theorems below.
attribute [local irreducible] BitOracleMachine.run

/-- Full source result for the unchanged nonce/transcript draw tuple, with the
encoded proof and saved-state words and all48 prior words retained. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  BitOracleReturnLink.embed tailLabel none (PrimeProgramOutputMachine.sourceResult slack g pk vote s live out)

/-- The encoded return pair matches the original first proof request. -/
theorem source_outputs {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgramProofSource.State (p:=p) (q:=q))
    (live : PrimeProgramProofSource.Cache (p:=p) (q:=q))
    (out : PrimeProgramProofSource.Draws (q:=q)) :
    let op := s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)
    let cfg := sourceResult slack g pk vote s live out
    cfg.stk 48 = (ballotProofBitCodec p q).encode op.1 ∧
    cfg.stk 49 = (ballotBothCachesBitCodec p q).encode (op.2,live) :=
  PrimeProgramOutputMachine.source_outputs slack g pk vote s live out

/-- All existing resident words remain, including the nonce pair, updated
cache/flag/history and original raw context. -/
theorem source_retained {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgramProofSource.State (p:=p) (q:=q))
    (live : PrimeProgramProofSource.Cache (p:=p) (q:=q))
    (out : PrimeProgramProofSource.Draws (q:=q)) (k : Fin 48) :
    (sourceResult slack g pk vote s live out).stk ⟨k.val,by omega⟩ =
      (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk k :=
  PrimeProgramOutputMachine.source_retained slack g pk vote s live out k

#print axioms source_outputs
#print axioms source_retained

private theorem tail_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
      BitOracleMachine.run PrimeProgramOutputMachine.code (PrimeProgramOutputMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
        (PrimeProgramOutputMachine.start (PrimeProgramCaller.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out) := by
  obtain ⟨c,_,he⟩ := PrimeProgramOutputMachine.charged_source slack g pk vote s live out
  rw [he,map_pure]
  rfl

/-- One original raw tape executes the complete existing drawSource tree and
the canonical proof and updated-state encoding; encoding introduces no new queries. -/
theorem execution_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    Prod.fst <$> BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote s live <$>
          runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q)) := by
  rw [linked_run]
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  calc
    _ = (do
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeProgramCaller.code
        (PrimeProgramCaller.clock raw slack p q) (PrimeProgramCaller.start raw)
      (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
        BitOracleMachine.run PrimeProgramOutputMachine.code (PrimeProgramOutputMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
          (PrimeProgramOutputMachine.start cfg.stk)) := by
      simp only [raw,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [PrimeProgramCaller.execution_source]
      simp only [simulateQ_map,bind_map_left,tail_source]
      simp only [map_eq_bind_pure_comp,Function.comp_def]

/-- Physical execution starts with one raw input and blank work. The startup
and full-code execution bounds are derived, including the larger finite control. -/
theorem physical_run {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7 (some entry) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      (some ∘ sourceResult slack g pk vote s live) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins
            (runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q))) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  have hw := within slack limit g pk vote s live
  rw [start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 7 (some entry) 0 raw
    (clock raw slack p q) limit (cost raw slack p q) hw
  rw [←start_source,start_height,Nat.add_zero] at he
  refine ⟨startup,hs,?_⟩
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (execution_source slack g pk vote s live)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms execution_source
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeProgramOutputCaller
