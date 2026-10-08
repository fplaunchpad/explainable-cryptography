import ExplainableCrypto.Helios.Computational.PrimeRequestDrawsRun
import ExplainableCrypto.Helios.Computational.PrimeFullFieldSource

namespace ExplainableCrypto.Helios.Computational.PrimeRequestDraws
open OracleComp OracleSpec BitOracleMachine
variable {p q : Nat} [Fact p.Prime] [Fact q.Prime]
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
attribute [local irreducible] BitOracleMachine.run

def sourceStart (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (second context : List Bool) : Config :=
  start (SamplerOperands.input slack q []) (scalarEncode r) second (q-1).bits context
    p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits vote

def sourceResult (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (second context : List Bool) (cs : ZMod q × ZMod q × ZMod q × ZMod q) : Config :=
  PrimeHonestTranscriptCaller.result (scalarEncode cs.1) (scalarEncode cs.2.1)
    (scalarEncode cs.2.2.1) (scalarEncode cs.2.2.2) q.bits
    (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).1).val.bits
    (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).2).val.bits r.val.bits
    (SamplerOperands.input slack q []) (scalarEncode r) second (q-1).bits context
    p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits vote

private theorem scalar_cast_word (a : List Bool) :
    scalarEncode (bitsValue a : ZMod q) = uniformNatEncode (bitsValue a%q) := by
  simp only [scalarEncode,ZMod.val_natCast]

/-- The same resident code handles every typed witness, including nonce zero.
It samples only the transcript scalars and retains the supplied context. -/
theorem charged_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (second context : List Bool) :
    ∃ charge : List Bool → List Bool → List Bool → List Bool → Nat,
      (∀ a, a.length = q.size+slack → ∀ b, b.length = q.size+slack →
        ∀ c, c.length = q.size+slack → ∀ d, d.length = q.size+slack →
        charge a b c d ≤ cost slack p q) ∧
      BitOracleMachine.run code (clock slack p q) (sourceStart slack g pk vote r second context) = (do
        let a ← CoinWordLoader.word (q.size+slack)
        let b ← CoinWordLoader.word (q.size+slack)
        let c ← CoinWordLoader.word (q.size+slack)
        let d ← CoinWordLoader.word (q.size+slack)
        pure (sourceResult slack g pk vote r second context
          ((bitsValue a : ZMod q),(bitsValue b : ZMod q),(bitsValue c : ZMod q),(bitsValue d : ZMod q)),
          charge a b c d)) := by
  obtain ⟨charge,hc,he⟩ := charged slack p q (primeGroupCoordinate g).val
    (primeGroupCoordinate pk).val r.val (Fact.out : p.Prime).two_le
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) second (q-1).bits context vote
  have ha := congrArg Prod.fst (PrimeEncryptMachine.coordinate_values g pk r vote)
  have hb := congrArg Prod.snd (PrimeEncryptMachine.coordinate_values g pk r vote)
  dsimp only at ha hb
  refine ⟨charge,hc,?_⟩
  change BitOracleMachine.run code (clock slack p q)
    (start (SamplerOperands.input slack q []) (uniformNatEncode r.val) second (q-1).bits
      context p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits vote) = _
  rw [he]
  apply bind_congr
  intro a
  apply bind_congr
  intro b
  apply bind_congr
  intro c
  apply bind_congr
  intro d
  simp only [result,sourceResult,scalarEncode,ZMod.val_natCast,ha,hb]

theorem execution_source (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (second context : List Bool) :
    Prod.fst <$> BitOracleMachine.run code (clock slack p q)
      (sourceStart slack g pk vote r second context) =
      simulateQ CoinWordLoader.liftCoins
        (sourceResult slack g pk vote r second context <$>
          runFairBitUniform slack (PrimeFullFieldSource.drawTranscriptScalars q)) := by
  obtain ⟨charge,_,he⟩ := charged_source slack g pk vote r second context
  rw [he]
  let W := (fun bits => uniformNatEncode (bitsValue bits%q)) <$>
    CoinWordLoader.word (q.size+slack)
  have hW := PrimeFullFieldSource.scalar_word_source q slack
  change W = _ at hW
  calc
    _ = (do
      let c ← W
      let e ← W
      let z0 ← W
      let z1 ← W
      pure (PrimeHonestTranscriptCaller.result c e z0 z1 q.bits
        (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).1).val.bits
        (primeGroupCoordinate (encryptWith g pk r (voteScalar vote)).2).val.bits r.val.bits
        (SamplerOperands.input slack q []) (scalarEncode r) second (q-1).bits context
        p.bits (primeGroupCoordinate g).val.bits (primeGroupCoordinate pk).val.bits vote)) := by
      simp only [W,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,
        sourceResult,scalar_cast_word]
    _ = _ := by
      rw [hW]
      simp only [PrimeFullFieldSource.drawTranscriptScalars,runFairBitUniform,simulateQ_bind,
        simulateQ_pure,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sourceResult]

theorem run_support (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (r : ZMod q)
    (second context : List Bool) :
    ∀ last ∈ support (BitOracleMachine.run code (clock slack p q)
      (sourceStart slack g pk vote r second context)), last.1.l = none ∧ last.2 ≤ cost slack p q := by
  obtain ⟨charge,hc,he⟩ := charged_source slack g pk vote r second context
  rw [he]
  intro last hl
  rw [mem_support_bind_iff] at hl; obtain ⟨a,ha,hl⟩ := hl
  rw [mem_support_bind_iff] at hl; obtain ⟨b,hb,hl⟩ := hl
  rw [mem_support_bind_iff] at hl; obtain ⟨c,hc',hl⟩ := hl
  rw [mem_support_bind_iff] at hl; obtain ⟨d,hd,hl⟩ := hl
  obtain rfl := eq_of_mem_support_pure _ hl
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)
    c (CoinWordLoader.word_length _ _ hc') d (CoinWordLoader.word_length _ _ hd)⟩

#print axioms charged_source
#print axioms execution_source
#print axioms run_support
end ExplainableCrypto.Helios.Computational.PrimeRequestDraws
