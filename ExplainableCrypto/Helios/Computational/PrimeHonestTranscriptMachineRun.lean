import ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine

namespace ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
open Turing.TM2 OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- The actual success guard and framed full-field sampler preserve every saved
word and derive their joint charge from the executed constituent operations. -/
theorem charged (slack q : Nat) (hq : 0 < q)
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (extra : Fin 3 → List Bool) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = q.size+slack → charge bits ≤ cost slack q) ∧
      BitOracleMachine.run code (clock slack q)
        (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote extra) =
      (fun bits =>
        (result (uniformNatEncode (bitsValue bits % q)) q.bits alpha beta nonce
          (SamplerOperands.input slack q []) first second samplerMod context modulus g pk vote extra,
          charge bits)) <$> CoinWordLoader.word (q.size+slack) := by
  obtain ⟨c,hc,he⟩ := CacheHashMachine.sample_run slack q hq beta alpha context
  refine ⟨fun bits => 3+c bits,?_,?_⟩
  · intro bits hb
    exact Nat.add_le_add_left (hc bits hb) 3
  · unfold clock
    rw [Nat.add_comm 1,BitOracleMachine.run,entry_step]
    simp only [pure_bind]
    rw [BitOracleReturnLink.rename_run _ _ _ sample_code]
    unfold samplerCode
    rw [BitOracleStackFrame.run,he]
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sample_result]

#print axioms charged
end ExplainableCrypto.Helios.Computational.PrimeHonestTranscriptMachine
