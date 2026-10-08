import ExplainableCrypto.Helios.Computational.ElectionDDHReduction
import Mathlib.Tactic.NormNum.Prime

/-! Non-vacuous finite reduction instances and independently calculated loss
controls. The finite fixture group carries no DDH hardness assertion. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHReductionControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionDDHSource
local instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩
private abbrev Scalar := ZMod 65537
private def key : Key Scalar := .key 1 3 4
private def prepare : Comp Scalar Scalar (Scalar × Scalar) := do
  let a ← ask key
  let b ← ask (.ballot ⟨1,3,(2,7)⟩ ((4,1),(8,2)))
  pure (a,b)
private def adversary (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar) :
    Adversary Scalar Scalar Scalar where
  castBallot before := do
    let a ← ask key
    pure (b,a+initial.1+initial.2+(before.board.length : Scalar))
  guessVote saved view := do
    let a ← ask (.key 1 3 (view.decryptionShares 0))
    pure (decide (saved+a = view.decryptionShares 1))
private def fingerprint (p : PublicParameters Scalar Scalar) := p.trusteeKeyProof.response.val

private theorem prepare_hash : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 2 := by
  simp [prepare,ask,key,ElectionCacheBudget.isHash]
private theorem cast_hash (b : Ballot Scalar Scalar 2) (initial : Scalar × Scalar)
    (before : PublicPrefix Scalar Scalar) :
    ((adversary b initial).castBallot before).IsQueryBoundP (ElectionCacheBudget.isHash (F := Scalar)) 1 := by
  simp [adversary,ask,ElectionCacheBudget.isHash]
private theorem generator_injective : Function.Injective (fun r : Scalar => r • (1:Scalar)) := by
  intro a b h
  simpa [smul_eq_mul] using h

/-- Actual historical game, shared querying preparation, public-view-dependent
casting state and querying guesser, with finite extraction parameters. -/
theorem complete_queried (b : Ballot Scalar Scalar 2) :
    |(Pr[fun out => out.1 = true | run (preparedGame fingerprint 1 prepare (adversary b)) ∅]).toReal-1/2| ≤
      18*(noncePointBound Scalar).toReal+3*((11*(2:ℝ)+2*1+131)/(Fintype.card Scalar:ℝ))+
      2*(16:ℝ)⁻¹+
      DiffieHellman.ddhDistAdvantage (1:Scalar) (ballotSecrecyDistinguisher fingerprint prepare (adversary b) 12 16)+
      DiffieHellman.ddhDistAdvantage (1:Scalar) (honestRejectDistinguisher fingerprint prepare (adversary b)) :=
  by
  simpa only [Nat.cast_ofNat,Nat.cast_one,Nat.reduceAdd] using
    prepared_ballot_secrecy_ddh_bound fingerprint 1 generator_injective prepare (adversary b)
      2 1 16 prepare_hash (cast_hash b) (by decide) (by norm_num [Scalar,ZMod.card])

/-- The arithmetic allowance, excluding the explicitly retained DDH advantages,
is strictly below the maximal winning bias 1/2. No hardness is asserted here. -/
theorem allowance_nonvacuous :
    18*(noncePointBound Scalar).toReal+3*((11*(2:ℝ)+2*1+131)/(Fintype.card Scalar:ℝ))+
      2*(16:ℝ)⁻¹ < 1/2 := by
  norm_num [noncePointBound,Scalar,ZMod.card]

/-- Cost of that same actual DDH algorithm, including preparation, every replay,
publication and the final view-dependent guessing query. -/
theorem complete_cost (b : Ballot Scalar Scalar 2) (g pk A T : Scalar) :
    (ballotSecrecyDistinguisher fingerprint prepare (adversary b) 12 16 g pk A T).IsTotalQueryBound
      ((1+3*(3456*13^3*16^4))*90+8) := by
  apply ballotSecrecy_prime_cost _ _ _ _ _ _ _ 12 16 2 1 1
  · exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩
  · intro initial before
    exact ⟨by norm_num,fun _ => trivial⟩
  · intro initial saved view
    exact ⟨by norm_num,fun _ => trivial⟩

/-- Two independently oriented comparison errors can both be necessary, even
when the two extracted-world probabilities coincide and rejection costs zero. -/
theorem both_extraction_losses_required :
    |(3/4:ℝ)-5/8| = 1/8 ∧ |(5/8:ℝ)-1/2| = 1/8 ∧
      |(3/4:ℝ)-1/2| = 2*(1/8) ∧ ¬ |(3/4:ℝ)-1/2| ≤ 1/8 := by
  norm_num

/-- Independent probability-chain controls against dropping the original loss,
using a signed advantage, or halving a two-game DDH advantage. -/
theorem advantage_losses_required :
    ¬ |(3/4:ℝ)-1/2| ≤ 0 ∧
      ¬ |(1/4:ℝ)-1/2| ≤ (1/4-1/2) ∧
      ¬ |(1/4:ℝ)-1/2| ≤ |(1/4:ℝ)-1/2|/2 := by
  norm_num

/-- A zero generator cannot satisfy the actual reduction's injectivity premise.
This excludes a degenerate group observation from a hardness instantiation. -/
theorem zero_generator_excluded : ¬ Function.Injective (fun r : Scalar => r • (0:Scalar)) := by
  intro h
  have he : (1:Scalar) = 0 := h (by simp)
  exact one_ne_zero he

#print axioms complete_queried
#print axioms allowance_nonvacuous
#print axioms complete_cost
#print axioms both_extraction_losses_required
#print axioms advantage_losses_required
#print axioms zero_generator_excluded
end ExplainableCrypto.Helios.Computational.ElectionDDHReductionControls
