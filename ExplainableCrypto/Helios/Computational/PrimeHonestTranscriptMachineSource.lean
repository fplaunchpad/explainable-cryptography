import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachineRun
import ExplainableCrypto.Helios.Computational.PrimeFullFieldSource

namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Full first-simulator-draw result over the exact retained caller words.
The enclosing raw-input theorem supplies the origin of the statement and frame. -/
def sourceResult (slack q : Nat)
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) (c : ZMod q) : Config :=
  result (scalarEncode c) q.bits alpha beta nonce (SamplerOperands.input slack q [])
    first second samplerMod context modulus g pk vote extra

/-- The actual reached-state controller executes the first full-field simulator
query, preserving its complete frame and source query tree. -/
theorem execution_source (slack q : Nat) [NeZero q]
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    Prod.fst <$> BitOracleMachine.run code (clock slack q)
      (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod
        context modulus g pk vote extra) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack q alpha beta nonce first second samplerMod context modulus g pk vote extra <$>
          runFairBitUniform slack (uniformSample (ZMod q))) := by
  obtain ⟨charge,_,he⟩ := charged slack q (Nat.pos_of_ne_zero (NeZero.ne q))
    alpha beta nonce first second samplerMod context modulus g pk vote extra
  rw [he]
  change _ = simulateQ CoinWordLoader.liftCoins
    ((fun c : ZMod q => result (scalarEncode c) q.bits alpha beta nonce (SamplerOperands.input slack q [])
      first second samplerMod context modulus g pk vote extra) <$>
      runFairBitUniform slack (uniformSample (ZMod q)))
  have h := congrArg (fun oa : OracleComp spec (List Bool) =>
      (fun word => result word q.bits alpha beta nonce (SamplerOperands.input slack q [])
        first second samplerMod context modulus g pk vote extra) <$> oa)
    (PrimeFullFieldSource.scalar_word_source q slack)
  simpa only [Functor.map_map,simulateQ_map,Function.comp_def,sourceResult] using h

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

/-- The local termination and charge contract follows from every actual branch. -/
theorem within (slack q limit : Nat) [NeZero q]
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    BitOracleLoopBounded.Within limit (cost slack q)
      (BitOracleMachine.run code (clock slack q)
        (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod
          context modulus g pk vote extra)) := by
  obtain ⟨charge,hc,he⟩ := charged slack q (Nat.pos_of_ne_zero (NeZero.ne q))
    alpha beta nonce first second samplerMod context modulus g pk vote extra
  apply within_support
  rw [he]
  intro out ho
  rw [support_map] at ho
  obtain ⟨bits,hb,rfl⟩ := ho
  exact ⟨rfl,hc bits (CoinWordLoader.word_length _ _ hb)⟩

#print axioms execution_source
#print axioms within
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
