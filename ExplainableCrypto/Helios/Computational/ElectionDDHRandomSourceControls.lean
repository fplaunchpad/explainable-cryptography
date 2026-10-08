import ExplainableCrypto.Helios.Computational.ElectionDDHRandomSource
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtractionControls

/-! Actual querying-game instances and controls for the uniform-mask and
hidden-vote boundaries. Finite fields are fixtures, not hardness assumptions. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHRandomSourceControls
open OracleComp OracleSpec ElectionOracle ElectionDDHSource ElectionProgrammedExtractionControls
local instance : Fact (Nat.Prime 257) := ⟨by decide +kernel⟩

/-- Querying preparation, saved casting state and querying guessing all remain
in the exact one-half result, at an arbitrary supplied initial source/cache. -/
theorem querying_complete (b : Ballot Scalar Scalar 2)
    (s : ElectionProgrammedSource.State Scalar Scalar) (live : BallotOracleCache Scalar Scalar) :
    Pr[fun out => out.1.1.2 = true | do
      let z ← uniformSample Scalar
      ElectionProgrammedSource.evaluate
        (completedReal (F := Scalar) (fun p => p.trusteeKeyProof.response.val) 1 (3:Scalar) 2 (z • 1) 3
          prepare (adversary b)) s live] = (2:ENNReal)⁻¹ :=
  completed_random_win _ _ _ _ _ _ _ s live

private def priorState : ElectionProgrammedSource.State Scalar Scalar :=
  ⟨(∅ : Cache Scalar Scalar).cacheQuery key 7,true,[statement]⟩
private def priorLive : BallotOracleCache Scalar Scalar :=
  (∅ : BallotOracleCache Scalar Scalar).cacheQuery (statement,commitment) 7

/-- A nonempty live cache and auxiliary answer precede the actual querying
callbacks; the theorem does not require clearing either one. -/
theorem prior_cache_complete (b : Ballot Scalar Scalar 2) :
    Pr[fun out => out.1.1.2 = true | do
      let z ← uniformSample Scalar
      ElectionProgrammedSource.evaluate
        (completedReal (F := Scalar) (fun p => p.trusteeKeyProof.response.val) 1 (3:Scalar) 2 (z • 1) 3
          prepare (adversary b)) priorState priorLive] = (2:ENNReal)⁻¹ :=
  querying_complete b _ _

private def viewing (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar) :
    Adversary Scalar Scalar Scalar where
  castBallot before := do
    let a ← ask key
    pure (b,a+initial.1+initial.2+(before.board.length : Scalar))
  guessVote saved view := do
    let a ← ask (.key 1 3 (view.decryptionShares 0))
    pure (decide (a+saved = view.decryptionShares 1))

/-- Public board length affects saved state; published shares select a later
oracle query and affect the final guess. The exact complete-game theorem covers
these view-dependent callbacks, too. -/
theorem view_dependent_complete (b : Ballot Scalar Scalar 2) :
    Pr[fun out => out.1.1.2 = true | do
      let z ← uniformSample Scalar
      ElectionProgrammedSource.evaluate
        (completedReal (F := Scalar) (fun p => p.trusteeKeyProof.response.val)
          1 (3:Scalar) 2 (z • 1) 3 prepare (viewing b)) .empty ∅] = (2:ENNReal)⁻¹ :=
  completed_random_win _ _ _ _ _ _ _ _ _

/-- The ciphertext observation itself distinguishes the two fixed-zero-mask
inputs. This is a masking control, not a complete attack-probability theorem. -/
theorem fixed_mask_ciphertext_leaks :
    (ElectionDDHConstruction.paired (F := Scalar) (1:Scalar) 3 2 0 5 7 9 false).1.1 0 ≠
      (ElectionDDHConstruction.paired (F := Scalar) (1:Scalar) 3 2 0 5 7 9 true).1.1 0 := by
  decide +kernel

/-- Uniformity removes that distinction even with retained column nonce sums. -/
theorem uniform_mask_both_votes :
    evalSPMF (do let z ← uniformSample Scalar
                 pure (ElectionDDHConstruction.paired (F := Scalar) (1:Scalar) 3 2 (z • 1) 5 7 9 false)) =
      evalSPMF (do let z ← uniformSample Scalar
                   pure (ElectionDDHConstruction.paired (F := Scalar) (1:Scalar) 3 2 (z • 1) 5 7 9 true)) :=
  ElectionDDHConstruction.paired_ciphertexts_random_eq _ _ _ _ _ _ _

/-- A caller handed the hidden vote guesses it with certainty. The complete
comparison's callback interface must therefore keep that bit private. -/
theorem leaked_vote_wins :
    Pr[= true | do let vote ← uniformSample Bool; pure (decide (vote=vote))] = 1 := by
  simp

#print axioms view_dependent_complete
#print axioms querying_complete
#print axioms prior_cache_complete
#print axioms fixed_mask_ciphertext_leaks
#print axioms uniform_mask_both_votes
#print axioms leaked_vote_wins
end ExplainableCrypto.Helios.Computational.ElectionDDHRandomSourceControls
