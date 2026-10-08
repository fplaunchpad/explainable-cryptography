import ExplainableCrypto.Helios.Computational.PrimeSimKeyCallerRun

namespace ExplainableCrypto.Helios.Computational.PrimeSimKeyCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
-- Keep proof-side unification from executing the concrete arithmetic clock.
-- Execution is rewritten only through the checked run theorems below.
attribute [local irreducible] BitOracleMachine.run

/-- Full source result for the unchanged nonce/transcript draw tuple, with the
exact original full hash-key word on 43 and all 43 prior words retained. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  BitOracleReturnLink.embed tailLabel none (PrimeSimKeyMachine.sourceResult slack g pk vote saved out)

/-- The new word is the complete existing statement-and-commitment key codec. -/
theorem source_key {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (sourceResult slack g pk vote saved out).stk 43 =
      (ballotKeyBitCodec p q).encode (PrimeSimKeySource.key g pk vote out) := rfl

/-- All existing words remain literal, including the four commitment values. -/
theorem source_retained {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q))
    (k : Fin 43) :
    (sourceResult slack g pk vote saved out).stk k.castSucc =
      (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk k := by
  fin_cases k <;> rfl

#print axioms source_key
#print axioms source_retained

private theorem tail_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) :
    (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
      BitOracleMachine.run PrimeSimKeyMachine.code (PrimeSimKeyMachine.clock p)
        (PrimeSimKeyMachine.start (PrimeSimAllCommitCaller.sourceResult slack g pk vote saved out).stk) =
      pure (sourceResult slack g pk vote saved out) := by
  obtain ⟨c,_,he⟩ := PrimeSimKeyMachine.charged_source slack g pk vote saved out
  rw [he,map_pure]
  rfl

/-- One original raw tape executes the complete existing drawSource tree and
the exact full key serialization; encoding introduces no new queries. -/
theorem execution_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    Prod.fst <$> BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote saved)) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote saved <$>
          runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q)) := by
  rw [linked_run]
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  calc
    _ = (do
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeSimAllCommitCaller.code
        (PrimeSimAllCommitCaller.clock raw slack p q) (PrimeSimAllCommitCaller.start raw)
      (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
        BitOracleMachine.run PrimeSimKeyMachine.code (PrimeSimKeyMachine.clock p)
          (PrimeSimKeyMachine.start cfg.stk)) := by
      simp only [raw,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [PrimeSimAllCommitCaller.execution_source]
      simp only [simulateQ_map,bind_map_left,tail_source]
      simp only [map_eq_bind_pure_comp,Function.comp_def]

/-- Physical execution starts with one raw input and blank work. The startup
and full-code execution bounds are derived, including the larger finite control. -/
theorem physical_run {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    let raw := PrimeHonestInputMachine.input g pk slack vote saved
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7 (some entry) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      (some ∘ sourceResult slack g pk vote saved) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins
            (runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q))) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  have hw := within slack limit g pk vote saved
  rw [start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 7 (some entry) 0 raw
    (clock raw slack p q) limit (cost raw slack p q) hw
  rw [←start_source,start_height,Nat.add_zero] at he
  refine ⟨startup,hs,?_⟩
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (execution_source slack g pk vote saved)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms execution_source
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeSimKeyCaller
