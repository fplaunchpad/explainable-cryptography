import ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachineRun

/-! Joint source correspondence and physical execution from a raw input tape. -/
namespace ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Complete historical source result, retaining the actual original private
startup word as context, both sampled nonce prefixes and the computed ciphertext. -/
def sourceResult {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) (rs : ZMod q × ZMod q) : Config :=
  BitOracleReturnLink.embed callerLabel none
    (PrimeNonceCiphertextCaller.sourceResult slack g pk vote
      (PrimeHonestInputMachine.input g pk slack vote saved) rs)

/-- The actual outer source entry has one raw word and otherwise blank work. -/
theorem start_source (raw : List Bool) :
    start raw = BitOracleInitialInput.source 7
      (some (inputLabel (PrimeHonestInputMachine.copyLabel 0))) 0 raw := rfl

/-- The loaded source-stack height is the original raw input length. -/
theorem start_height (raw : List Bool) : TM2TapeRuns.height (start raw).stk = raw.length := by
  rw [start_source]
  unfold TM2TapeRuns.height
  apply le_antisymm
  · apply Finset.sup_le
    intro k _
    by_cases h : k = 7
    · subst k
      simp [BitOracleInitialInput.source]
    · simp [BitOracleInitialInput.source,Function.update,h]
  · have h := Finset.le_sup (f := fun k : Fin 23 =>
      ((BitOracleInitialInput.source (7 : Fin 23) (some (inputLabel (PrimeHonestInputMachine.copyLabel 0))) (0 : Fin 3) raw).stk k).length)
      (Finset.mem_univ (7 : Fin 23))
    simpa [BitOracleInitialInput.source] using h

/-- The actual initialized caller preserves the joint historical source tree,
including both fresh nonce draws and the complete original-input context. -/
theorem execution_source {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    Prod.fst <$> BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote saved)) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote saved <$> runFairBitUniform slack (drawPrimeNoncePair (q := q))) := by
  obtain ⟨c,_,he⟩ := linked_run g pk slack vote saved
  rw [he]
  have hc := congrArg (fun oa => BitOracleReturnLink.embed callerLabel none <$> oa)
    (PrimeNonceCiphertextCaller.execution_source slack g pk vote
      (PrimeHonestInputMachine.input g pk slack vote saved))
  change _ = simulateQ CoinWordLoader.liftCoins
    ((fun rs : ZMod q × ZMod q => BitOracleReturnLink.embed callerLabel none
      (PrimeNonceCiphertextCaller.sourceResult slack g pk vote
        (PrimeHonestInputMachine.input g pk slack vote saved) rs)) <$>
      runFairBitUniform slack (drawPrimeNoncePair (q := q)))
  simpa only [Functor.map_map,←simulateQ_map,Function.comp_def] using hc

private theorem within_support (limit bound : Nat) (oa : OracleComp spec (Config × Nat))
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

/-- Every actual branch halts with the derived combined initialization,
nonce-sampling, routing and ciphertext charge. -/
theorem within {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    BitOracleLoopBounded.Within limit
      (cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote saved))) := by
  obtain ⟨c,hc,he⟩ := charged g pk slack vote saved
  apply within_support
  rw [he]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨a,ha,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨b,hb,ho⟩ := ho
  have hv := eq_of_mem_support_pure _ ho
  subst out
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)⟩

/-- Physical execution starts with the original raw input tape and blank work.
The loader's actual startup cost is derived and the complete joint source tree
is returned under the existing bounded oracle adapter. -/
theorem physical_run {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    let raw := PrimeHonestInputMachine.input g pk slack vote saved
    let B := cost raw slack p q
    let T := BitOracleTapeCap.unitCost (raw.length+B)*B*BitOraclePrimitiveLoop.globalFactor code
    ∃ startup ≤ 4*raw.length+8,
      BitOracleInitialInput.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
        (BitOracleInitialInput.run code 7
          (some (inputLabel (PrimeHonestInputMachine.copyLabel 0))) 0
          (startup+T) (BitOracleInitialInput.initial raw)) =
      (some ∘ sourceResult slack g pk vote saved) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (drawPrimeNoncePair (q := q)))) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  have hw := within slack limit g pk vote saved
  rw [start_source] at hw
  obtain ⟨startup,hs,he⟩ := BitOracleInitialInput.run_source_bounded code 7
    (some (inputLabel (PrimeHonestInputMachine.copyLabel 0))) 0 raw
    (clock raw slack p q) limit (cost raw slack p q) hw
  rw [←start_source,start_height,Nat.add_zero] at he
  refine ⟨startup,hs,?_⟩
  rw [he]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (execution_source slack g pk vote saved)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms start_source
#print axioms start_height
#print axioms execution_source
#print axioms within
#print axioms physical_run
end ExplainableCrypto.Helios.Computational.PrimeHonestCiphertextMachine
