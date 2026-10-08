import ExplainableCrypto.Helios.Computational.PrimeTranscriptDrawsRun
import ExplainableCrypto.Helios.Computational.PrimeFullFieldSource

/-! Complete four-field simulator source and derived bounded execution. -/
namespace ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- Complete stored four-scalar result, retaining the exact reached caller frame. -/
def sourceResult (slack q : Nat)
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool)
    (vote : Bool) (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  result (scalarEncode cs.1) (scalarEncode cs.2.1) (scalarEncode cs.2.2.1) (scalarEncode cs.2.2.2)
    q.bits alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod
    context modulus g pk vote

/-- The actual four-call controller preserves the joint source query tree.
The separately checked factor equation connects that tuple source to the
existing programmed transcript before commitment arithmetic. -/
theorem execution_source (slack q : Nat) [NeZero q]
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    Prod.fst <$> BitOracleMachine.run code (clock slack q)
      (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod
        context modulus g pk vote) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack q alpha beta nonce first second samplerMod context modulus g pk vote <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨charge,_,he⟩ := charged slack q (Nat.pos_of_ne_zero (NeZero.ne q))
    alpha beta nonce first second samplerMod context modulus g pk vote
  rw [he]
  let W := (fun bits => uniformNatEncode (bitsValue bits % q)) <$>
    CoinWordLoader.word (q.size+slack)
  have hW := PrimeFullFieldSource.scalar_word_source q slack
  change W = _ at hW
  calc
    _ = (do
      let c ← W
      let e ← W
      let z0 ← W
      let z1 ← W
      pure (result c e z0 z1 q.bits alpha beta nonce (SamplerOperands.input slack q [])
        first second samplerMod context modulus g pk vote)) := by
      simp only [W,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [hW]
      simp only [PrimeFullFieldSource.drawTranscriptScalars,runFairBitUniform,simulateQ_bind,
        simulateQ_pure,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sourceResult]

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

/-- All four actual draws and three consumed saves satisfy the derived aggregate
termination/charge contract for every bounded-oracle adapter limit. -/
theorem within (slack q limit : Nat) [NeZero q]
    (alpha beta nonce first second samplerMod context modulus g pk : List Bool) (vote : Bool) :
    BitOracleLoopBounded.Within limit (cost slack q)
      (BitOracleMachine.run code (clock slack q)
        (start alpha beta nonce (SamplerOperands.input slack q []) first second samplerMod
          context modulus g pk vote)) := by
  obtain ⟨charge,hc,he⟩ := charged slack q (Nat.pos_of_ne_zero (NeZero.ne q))
    alpha beta nonce first second samplerMod context modulus g pk vote
  apply within_support
  rw [he]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨c,hc',ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨e,he',ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨z0,hz0,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨z1,hz1,ho⟩ := ho
  have h := eq_of_mem_support_pure _ ho
  subst out
  exact ⟨rfl,hc c (CoinWordLoader.word_length _ _ hc') e (CoinWordLoader.word_length _ _ he')
    z0 (CoinWordLoader.word_length _ _ hz0) z1 (CoinWordLoader.word_length _ _ hz1)⟩

#print axioms execution_source
#print axioms within
end ExplainableCrypto.Helios.Computational.PrimeTranscriptDraws
