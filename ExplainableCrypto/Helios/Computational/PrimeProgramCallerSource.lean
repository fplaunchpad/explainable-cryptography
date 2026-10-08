import ExplainableCrypto.Helios.Computational.PrimeProgramCallerRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgramCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
-- Keep proof-side unification from executing the concrete arithmetic clock.
-- Execution is rewritten only through the checked run theorems below.
attribute [local irreducible] BitOracleMachine.run

/-- Full source result for the unchanged nonce/transcript draw tuple, with the
executed cache, sticky flag and ordered history update. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  BitOracleReturnLink.embed tailLabel none (PrimeProgramMachine.sourceResult slack g pk vote s live out)

/-- Exact resident state.program successor reached by the raw caller. -/
theorem source_state {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) :
    let next := (s.program (PrimeSimKeySource.key g pk vote out).1
      (PrimeProgrammedInsertSource.transcript g pk vote out)).2
    let cfg := sourceResult slack g pk vote s live out
    cfg.stk 44 = (ballotCacheBitCodec p q).encode next.cache ∧
    cfg.stk 46 = [next.bad] ∧
    cfg.stk 45 = (ballotCacheBitCodec p q).encode live ∧
    cfg.stk 47 = (ballotStatementBitCodec p q).list.encode next.programmed :=
  PrimeProgramMachine.source_state slack g pk vote s live out

/-- Unchanged resident words include the original raw context, nonces and
challenge/key. Ports44/46/47 carry the updated state independently of raw14. -/
theorem source_retained {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool)
    (s : PrimeProgrammedInsertSource.State (p:=p) (q:=q))
    (live : PrimeProgrammedInsertSource.Cache (p:=p) (q:=q))
    (out : PrimeProgrammedInsertSource.Draws (q:=q)) (k : Fin 48)
    (h44 : k ≠ 44) (h46 : k ≠ 46) (h47 : k ≠ 47) :
    (sourceResult slack g pk vote s live out).stk k =
      (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk k := by
  change (Function.update (Function.update (Function.update _ 44 _) 46 _) 47 _) k = _
  simp only [Function.update_of_ne h47,Function.update_of_ne h46,Function.update_of_ne h44]

#print axioms source_state
#print axioms source_retained

private theorem tail_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
      BitOracleMachine.run PrimeProgramMachine.code (PrimeProgramMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
        (PrimeProgramMachine.start (PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out).stk) =
      pure (sourceResult slack g pk vote s live out) := by
  obtain ⟨c,_,he⟩ := PrimeProgramMachine.charged_source slack g pk vote s live out
  rw [he,map_pure]
  rfl

/-- One original raw tape executes the complete existing drawSource tree and
executed programming transition; the transition introduces no new queries. -/
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
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeProgrammedStateCaller.code
        (PrimeProgrammedStateCaller.clock raw slack p q) (PrimeProgrammedStateCaller.start raw)
      (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
        BitOracleMachine.run PrimeProgramMachine.code (PrimeProgramMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
          (PrimeProgramMachine.start cfg.stk)) := by
      simp only [raw,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [PrimeProgrammedStateCaller.execution_source]
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
end ExplainableCrypto.Helios.Computational.PrimeProgramCaller
