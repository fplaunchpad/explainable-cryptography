import ExplainableCrypto.Helios.Computational.BallotReplayParameters
import ExplainableCrypto.Helios.Computational.ElectionDDHSourceCost

/-! The same executable parameters instantiate the complete source comparison
and its derived interaction cost. No acceptance event is conditioned away. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (evaluate)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual complete-output error with the integer repetition count. The only
remaining additive event here is actual honest rejection; its DDH transfer is
proved in `ElectionDDHRejection`. -/
theorem extracted_finish_accuracy {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g A T : G) (hg : g ≠ 0) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (p c e : Nat)
    (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c)
    (he : 0 < e) (hq : 12*(p+c+10)*e ≤ Fintype.card F) :
    ENNReal.ofReal (tvDist
      (extractedGame fingerprint g (secret • g) A T prepare adversary (p+c+9)
        (ballotReplayTrials (p+c+9) e))
      (evaluate (completedReal fingerprint g (secret • g) A T secret prepare adversary) .empty ∅)) ≤
      Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
        runBallotOracle (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅] +
        (e:ENNReal)⁻¹ := by
  have h := extracted_finish_distance_le fingerprint g A T hg secret prepare adversary p c
    (ballotReplayTrials (p+c+9) e) hp hc (6*((p+c+9:Nat)+1)*e : ENNReal)⁻¹
  apply h.trans
  apply add_le_add le_rfl
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    ballotReplay_parameters (p+c+9) (Fintype.card F) e he (by simpa only [Nat.add_assoc] using hq)

/-- Cost of that same choice, using the pinned prime-field sampler. This is an
explicit polynomial in the live budget, accuracy request and callback query
budgets. It counts uniform-index oracle nodes, not local bit operations. -/
theorem extractedGame_accuracy_cost {q : Nat} [Fact q.Prime] {H : Type}
    [AddCommGroup H] [Module (ZMod q) H] [DecidableEq H] {Init Saved : Type}
    (fingerprint : PublicParameters (ZMod q) H → Nat) (g pk A T : H)
    (prepare : Comp (ZMod q) H Init) (adversary : Init → Adversary (ZMod q) H Saved)
    (N e P C D : Nat) (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C)
    (hd : ∀ initial saved view, ((adversary initial).guessVote saved view).IsTotalQueryBound D) :
    (extractedGame fingerprint g pk A T prepare adversary N (ballotReplayTrials N e)).IsTotalQueryBound
      ((1+3*(3456*(N+1)^3*e^4))*(4*P+4*C+78)+(4+4*D)) :=
  extractedGame_prime_total_bound fingerprint g pk A T prepare adversary N
    (ballotReplayTrials N e) P C D hp hc hd

#print axioms extracted_finish_accuracy
#print axioms extractedGame_accuracy_cost
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
