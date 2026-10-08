import ExplainableCrypto.Helios.Computational.CacheCallerCoins
import ExplainableCrypto.Helios.Computational.PrimeSamplers

/-! Exact query-tree interface for the full-field simulator's scalar draws. -/
namespace ExplainableCrypto.Helios.Computational.PrimeFullFieldSource
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- The actual ZMod sampler uses the existing finite uniform source. -/
theorem uniform_zmod (q slack : Nat) [NeZero q] :
    runFairBitUniform slack (uniformSample (ZMod q)) =
      (ZMod.finEquiv q) <$> sampleFairBitRange q slack := by
  change runFairBitUniform slack ((ZMod.finEquiv q) <$> uniformSample (Fin q)) = _
  simp only [runFairBitUniform,simulateQ_map]
  rw [←runFairBitUniform,CacheCallerCoins.uniform_eq]

private theorem encode_fin (q : Nat) [NeZero q] (i : Fin q) :
    scalarEncode ((ZMod.finEquiv q) i) = uniformNatEncode i.val := by
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

/-- The chronological coin word produces the complete encoded scalar source
query tree. Modulo q includes zero; this is not the nonzero nonce sampler. -/
theorem scalar_word_source (q slack : Nat) [NeZero q] :
    (fun bits => uniformNatEncode (bitsValue bits % q)) <$>
      CoinWordLoader.word (q.size+slack) =
      simulateQ CoinWordLoader.liftCoins
        (scalarEncode <$> runFairBitUniform slack (uniformSample (ZMod q))) := by
  rw [uniform_zmod]
  have h := congrArg (fun oa : OracleComp BitOracleMachine.spec Nat =>
    (fun n => uniformNatEncode (n % q)) <$> oa)
    (CoinWordLoader.word_index (q.size+slack))
  simpa only [Functor.map_map,simulateQ_map,sampleFairBitRange,sampleFairBitModulo,
    Function.comp_def,encode_fin] using h

#print axioms uniform_zmod
#print axioms scalar_word_source
end ExplainableCrypto.Helios.Computational.PrimeFullFieldSource

namespace ExplainableCrypto.Helios.Computational.PrimeFullFieldSource
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

/-- The four existing full-field source draws, retaining their chronological
joint result before the programmed simulator computes its commitments. -/
def drawTranscriptScalars (q : Nat) [NeZero q] :
    ProbComp (ZMod q × ZMod q × ZMod q × ZMod q) := do
  let c ← uniformSample (ZMod q)
  let e ← uniformSample (ZMod q)
  let z0 ← uniformSample (ZMod q)
  let z1 ← uniformSample (ZMod q)
  pure (c,e,z0,z1)

/-- The tuple source factors the actual existing programmed transcript.
This equation executes no commitment arithmetic in the bit machine. -/
theorem ballotFullSimTranscript_factor {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (stmt : BallotStatement (PrimeGroup p q)) :
    ballotFullSimTranscript (F := ZMod q) stmt =
      (fun cs : ZMod q × ZMod q × ZMod q × ZMod q =>
        (ballotSimCommit stmt cs.1 (cs.2.1,cs.2.2.1,cs.2.2.2),
          cs.1,(cs.2.1,cs.2.2.1,cs.2.2.2))) <$> drawTranscriptScalars q := by
  simp only [ballotFullSimTranscript,drawTranscriptScalars,map_bind,map_pure]

#print axioms ballotFullSimTranscript_factor
end ExplainableCrypto.Helios.Computational.PrimeFullFieldSource
