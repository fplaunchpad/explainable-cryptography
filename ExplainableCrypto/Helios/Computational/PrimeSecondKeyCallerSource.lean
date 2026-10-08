import ExplainableCrypto.Helios.Computational.PrimeSecondKeyCallerRun

namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
open OracleComp OracleSpec BitOracleMachine
open PrimeProgramProofSource (State Cache Draws)
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxHeartbeats 400000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  BitOracleReturnLink.embed tailLabel none
    (PrimeSecondKeyMachine.sourceResult slack g pk vote s live out cs)

/-- The original nonce/transcript tuple is sampled once. Only the second
proof's full-field transcript tuple is newly sampled after that prefix. -/
def sourceTree (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) := do
  let out ← runFairBitUniform slack (PrimeHonestTranscriptCaller.drawSource q)
  let cs ← runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)
  pure (sourceResult slack g pk vote s live out cs)

/-- Recover both sampled tuples from every supported prefix result. This is the
source-derived return interface needed by the next resident proof call. -/
theorem source_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (cfg : Config)
    (h : cfg ∈ support (simulateQ CoinWordLoader.liftCoins
      (sourceTree slack g pk vote s live))) :
    ∃ out : Draws (q:=q), ∃ cs : ZMod q × ZMod q × ZMod q × ZMod q,
      cfg = sourceResult slack g pk vote s live out cs := by
  rw [sourceTree,simulateQ_bind,mem_support_bind_iff] at h
  obtain ⟨out,_,h⟩ := h
  rw [simulateQ_bind,mem_support_bind_iff] at h
  obtain ⟨cs,_,h⟩ := h
  rw [simulateQ_pure] at h
  exact ⟨out,cs,eq_of_mem_support_pure _ h⟩

theorem source_retained (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) (k : Fin 70) :
    (sourceResult slack g pk vote s live out cs).stk ⟨k.val,by omega⟩ =
      (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk k :=
  PrimeSecondKeyMachine.source_retained slack g pk vote s live out cs k

private theorem tail_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) (out : Draws (q:=q))
    (cs : ZMod q × ZMod q × ZMod q × ZMod q) :
    (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
      BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
        (PrimeSecondKeyMachine.start (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk) =
      pure (sourceResult slack g pk vote s live out cs) := by
  obtain ⟨charge,_,he⟩ := PrimeSecondKeyMachine.charged_source slack g pk vote s live out cs
  change BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
    (PrimeSecondKeyMachine.start (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk) = _ at he
  rw [he,map_pure]
  rfl

/-- One original raw input executes the second ciphertext and fresh transcript,
then its complete original hash key. Serialization preserves the sampled tree,
updated saved state and first proof; no execution certificate is supplied. -/
theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    Prod.fst <$> BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))) =
      simulateQ CoinWordLoader.liftCoins (sourceTree slack g pk vote s live) := by
  rw [linked_run]
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  calc
    _ = (do
      let cfg ← Prod.fst <$> BitOracleMachine.run PrimeSecondAllCommitCaller.code
        (PrimeSecondAllCommitCaller.clock raw slack p q) (PrimeSecondAllCommitCaller.start raw)
      (fun last => BitOracleReturnLink.embed tailLabel none last.1) <$>
        BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
          (PrimeSecondKeyMachine.start cfg.stk)) := by
      simp only [raw,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [PrimeSecondAllCommitCaller.execution_source]
      simp only [PrimeSecondAllCommitCaller.sourceTree,sourceTree,simulateQ_bind,
        simulateQ_pure,bind_assoc,pure_bind,tail_source]

/-- Physical startup and the combined execution bound are derived from the
same raw input and actual finite code, with the same bounded oracle adapter. -/
theorem physical_run (slack limit : Nat) (g pk : PrimeGroup p q) (vote : Bool)
    (s : State (p:=p) (q:=q)) (live : Cache (p:=p) (q:=q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7 (some entry) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      some <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (simulateQ CoinWordLoader.liftCoins (sourceTree slack g pk vote s live)) := by
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
  simpa only [Functor.map_map,Function.comp_def] using congrArg (fun oa => some <$> oa) hr

#print axioms source_support
#print axioms source_retained
#print axioms execution_source
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
