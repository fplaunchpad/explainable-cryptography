import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCallerRun
import ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsSource

/-! Exact joint source law and physical execution from the original input. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
/-- The source tuple is precisely the two nonzero nonce draws followed by the
four full-field simulator draws; execution of commitments follows this prefix. -/
def drawSource (q : Nat) [Fact q.Prime] := do
  let rs ← drawPrimeNoncePair (q := q)
  let cs ← PrimeFullFieldSource.drawTranscriptScalars q
  pure (rs,cs)

/-- Source result retains the prior ciphertext and input context and stores
c,e,z0,z1 in the actual four scalar destinations. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q)) : Config :=
  let cfg := PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved out.1
  result (scalarEncode out.2.1) (scalarEncode out.2.2.1)
    (scalarEncode out.2.2.2.1) (scalarEncode out.2.2.2.2)
    q.bits (cfg.stk 17) (cfg.stk 0) (cfg.stk 13) (SamplerOperands.input slack q [])
    (cfg.stk 20) (cfg.stk 21) (cfg.stk 22) (cfg.stk 14) (cfg.stk 6)
    (cfg.stk 16) (cfg.stk 15) vote

end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem tail_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) (rs : ZMod q × ZMod q) :
    (fun out => BitOracleReturnLink.embed drawLabel none out.1) <$>
      BitOracleMachine.run PrimeTranscriptDraws.code (PrimeTranscriptDraws.clock slack q)
        (continuation (PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved rs) vote) =
      simulateQ CoinWordLoader.liftCoins
        ((fun cs => sourceResult slack g pk vote saved (rs,cs)) <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  let cfg := PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved rs
  have h := PrimeTranscriptDraws.execution_source slack q (cfg.stk 17) (cfg.stk 0)
    (cfg.stk 13) (cfg.stk 20) (cfg.stk 21) (cfg.stk 22) (cfg.stk 14)
    (cfg.stk 6) (cfg.stk 16) (cfg.stk 15) vote
  have hr : (PrimeHonestCiphertextMachine.sourceResult slack g pk vote saved rs).stk 19 =
      SamplerOperands.input slack q [] := rfl
  have hh := congrArg (fun oa => BitOracleReturnLink.embed drawLabel none <$> oa) h
  simpa only [Functor.map_map,simulateQ_map,Function.comp_def,
    PrimeTranscriptDraws.sourceResult,sourceResult,result,continuation,cfg,hr] using hh

/-- One raw-input execution preserves the complete joint source tree: both
historical nonce draws and all four full-field programmed simulator scalars. -/
theorem execution_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    Prod.fst <$> BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote saved)) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote saved <$> runFairBitUniform slack (drawSource q)) := by
  rw [linked_run]
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  calc
    _ = (do
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeHonestCiphertextMachine.code
        (PrimeHonestCiphertextMachine.clock raw slack p q) (PrimeHonestCiphertextMachine.start raw)
      (fun out => BitOracleReturnLink.embed drawLabel none out.1) <$>
        BitOracleMachine.run PrimeTranscriptDraws.code (PrimeTranscriptDraws.clock slack q)
          (continuation cfg vote)) := by
      simp only [raw,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [PrimeHonestCiphertextMachine.execution_source]
      simp only [simulateQ_map,bind_map_left,tail_source]
      simp only [drawSource,runFairBitUniform,simulateQ_bind,simulateQ_pure,
        map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- Actual physical execution starts with the original raw tape and blank
workspace. Both the startup bound and combined execution contract are derived. -/
theorem physical_run {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    let raw := PrimeHonestInputMachine.input g pk slack vote saved
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7
          (some (cipherLabel (PrimeHonestCiphertextMachine.inputLabel
            (PrimeHonestInputMachine.copyLabel 0)))) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      (some ∘ sourceResult slack g pk vote saved) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (drawSource q))) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  have hw := within slack limit g pk vote saved
  rw [start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 7
    (some (cipherLabel (PrimeHonestCiphertextMachine.inputLabel
      (PrimeHonestInputMachine.copyLabel 0)))) 0 raw
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
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptCaller
