import ExplainableCrypto.Helios.Computational.HonestBallotOracle
import ExplainableCrypto.Helios.Computational.BallotProgrammedControls

/-! Literal controls for coin regrouping, aggregate nonces and request provenance.
The independent Python gate constructs full multiplicative ballots modulo 23. -/
namespace ExplainableCrypto.Helios.Computational.HonestBallotOracleControls
open OracleComp OracleSpec StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def hash : StatementHash Scalar Scalar := fun _ _ _ _ => 5

def coins : HonestCoins Scalar := ⟨![1,10],![1,1,1],![1,1,2],![2,2,2]⟩
def transposedCoins : HonestCoins Scalar :=
  ⟨coins.nonce,![1,1,2],![1,1,2],![1,2,2]⟩

private theorem nonzero_supported (r : Scalar) (hr : r ≠ 0) : r ∈ support (sampleNonzero Scalar) := by
  simp only [sampleNonzero,support_map]
  exact ⟨Units.mk0 r hr,by simp,rfl⟩

private theorem triple_supported (a b c : Scalar) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ![a,b,c] ∈ support (drawTriple Scalar) := by
  simp only [drawTriple,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨a,nonzero_supported a ha,b,nonzero_supported b hb,c,nonzero_supported c hc,rfl⟩

theorem zero_aggregate_fixture_reachable : coins ∈ support (drawHonestCoins Scalar) := by
  simp only [drawHonestCoins,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  refine ⟨_,triple_supported 1 1 1 (by decide) (by decide) (by decide),
    _,triple_supported 1 1 2 (by decide) (by decide) (by decide),
    _,triple_supported 2 2 2 (by decide) (by decide) (by decide),(1,10),?_,rfl⟩
  simp only [drawNoncePair,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff]
  exact ⟨1,nonzero_supported 1 (by decide),10,nonzero_supported 10 (by decide),rfl⟩

theorem nonzero_components_zero_aggregate :
    coins.nonce 0 ≠ 0 ∧ coins.nonce 1 ≠ 0 ∧ coins.nonce 0 + coins.nonce 1 = 0 ∧
    (strongHonestBallot hash 1 3 false coins).aggregate = (0,0) := by decide

theorem zero_aggregate_ballot_valid :
    (strongHonestBallot hash 1 3 false coins).StrongValid hash 1 3 :=
  strongHonestBallot_valid hash 1 3 false coins

theorem explicit_coin_oracle_agrees :
    simulateQ (ballotFunctionImpl hash) (strongHonestBallotWithCoinsOracle 1 3 false coins) =
      pure (strongHonestBallot hash 1 3 false coins) :=
  strongHonestBallotWithCoinsOracle_function hash 1 3 false coins

/-- Nonzero sampling does not permit reusing one component nonce for the sum. -/
theorem wrong_aggregate_target :
    honestProofStatement (1 : Scalar) 3 (false,coins.nonce 0) ≠
      (strongHonestBallot hash 1 3 false coins).coveredStatement 1 3 none := by decide

/-- Leaving the nine coins in column order changes the actual full proof fields. -/
theorem missing_transpose_changes_ballot :
    strongHonestBallot hash 1 3 false coins ≠
      strongHonestBallot hash 1 3 false transposedCoins := by
  intro he
  have hd : ((strongHonestBallot hash 1 3 false coins).proof 0).one.a ≠
      ((strongHonestBallot hash 1 3 false transposedCoins).proof 0).one.a := by decide
  exact hd (congrArg (fun b : Ballot Scalar Scalar 2 => (b.proof 0).one.a) he)

theorem sampled_coin_distribution_preserved :
    𝒮[drawHonestCoinsByProof Scalar] = 𝒮[drawHonestCoins Scalar] :=
  drawHonestCoinsByProof_eq

theorem sampled_ballot_cache_and_flag_preserved :
    𝒮[runBallotProofReal 1 3 (strongHonestBallotOracle (F := Scalar) 1 3 false) (cached 6,true)] =
    𝒮[do let c ← drawHonestCoins Scalar
         let out ← runBallotOracle (strongHonestBallotWithCoinsOracle 1 3 false c) (cached 6)
         pure (out.1,(out.2,true))] :=
  strongHonestBallotOracle_real_eq 1 3 false (cached 6) true

/-- Earlier recorded requests remain after this ballot's three requests. -/
theorem previous_request_provenance_retained
    (out : (Ballot Scalar Scalar 2 × BallotProgrammedState Scalar Scalar) ×
      BallotOracleCache Scalar Scalar)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl 1 3)
      (strongHonestBallotOracle (F := Scalar) 1 3 false)).run
        BallotProgrammedControls.collisionState) (cached 6))) :
    out.1.2.programmed = [out.1.1.coveredStatement 1 3 none,
      out.1.1.coveredStatement 1 3 (some 1),out.1.1.coveredStatement 1 3 (some 0),stmt] := by
  exact strongHonestBallotOracle_request_targets 1 3 false
    BallotProgrammedControls.collisionState (cached 6) out ho

#print axioms zero_aggregate_fixture_reachable
#print axioms nonzero_components_zero_aggregate
#print axioms zero_aggregate_ballot_valid
#print axioms explicit_coin_oracle_agrees
#print axioms wrong_aggregate_target
#print axioms missing_transpose_changes_ballot
#print axioms sampled_coin_distribution_preserved
#print axioms sampled_ballot_cache_and_flag_preserved
#print axioms previous_request_provenance_retained
end ExplainableCrypto.Helios.Computational.HonestBallotOracleControls
