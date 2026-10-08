import ExplainableCrypto.Helios.Computational.TrusteeOracleSimulation
import ExplainableCrypto.Helios.Computational.ElectionCacheBudget

/-! The actual trustee proof steps after arbitrary bounded prior election
queries. The cache cover and tag injectivity are derived, not hypotheses. -/
namespace ExplainableCrypto.Helios.Computational.TrusteeReachableSimulation
open OracleComp OracleSpec ElectionOracle TrusteeOracleSimulation ElectionCacheBudget
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Public inputs suffice: the simulator does not take the secret key. -/
def keySim (g pk : G) := sim (F := F) g pk (Key.key g pk)

/-- Ciphertext and published share are retained in the actual hash context. -/
def partialSim (g pk : G) (ct : Ciphertext G) (share : G) :=
  sim (F := F) (g,ct.1) (pk,share) (Key.decryption g pk ct share)

omit [Field F] [Fintype F] [DecidableEq F] [AddCommGroup G] [Module F G] in
private theorem covered_after {A : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) : Covered out.2 n := by
  simpa using run_covered prior n 0 hb ∅ Covered.empty out ho

/-- The original nonzero-nonce key proof after a reachable prior run is within
(1+n)/|F| of the public-input simulator, including the complete final cache.
The nonce here is drawn at the proof step; original-election scheduling is a
separate composition obligation. -/
theorem key_after_queries_le {A : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) (g : G) (secret : F)
    (hg : Function.Injective (fun r : F => r • g)) :
    tvDist ((fun result => ((result.1,false),result.2)) <$>
      run (do let r ← liftProb (sampleNonzero F); keyWithCoins g secret r) out.2)
      ((keySim g (secret • g)).run out.2) ≤
        (1+(n : ℝ)) * (Fintype.card F : ℝ)⁻¹ := by
  obtain ⟨Q,hQ,hcover⟩ := covered_after prior n hb out ho
  have htag : Function.Injective (Key.key g (secret • g)) := by
    intro x y h; cases h; rfl
  rw [← key_real]
  exact (distance_le g secret _ htag hg out.2 Q hcover).trans (by gcongr)

/-- The original equality-of-logs proof has the same reachable-cache bound.
Generator injectivity suffices; exponentiation onto G×G need not be surjective. -/
theorem partial_after_queries_le {A : Type} (prior : Comp F G A) (n : Nat)
    (hb : prior.IsQueryBoundP (isHash (F := F)) n) (out : A × Cache F G)
    (ho : out ∈ support (run prior ∅)) (g : G) (secret : F) (ct : Ciphertext G)
    (hg : Function.Injective (fun r : F => r • g)) :
    tvDist ((fun result => ((result.1,false),result.2)) <$>
      run (do let r ← liftProb (sampleNonzero F); partialWithCoins g secret r ct) out.2)
      ((partialSim g (secret • g) ct (partialDecrypt secret ct)).run out.2) ≤
        (1+(n : ℝ)) * (Fintype.card F : ℝ)⁻¹ := by
  obtain ⟨Q,hQ,hcover⟩ := covered_after prior n hb out ho
  have htag : Function.Injective (Key.decryption g (secret • g) ct (partialDecrypt secret ct)) := by
    intro x y h; cases h; rfl
  rw [← partial_real]
  exact (distance_le (g,ct.1) secret _ htag
    (TrusteeSimulation.partial_injective g hg ct) out.2 Q hcover).trans (by gcongr)

#print axioms key_after_queries_le
#print axioms partial_after_queries_le
end ExplainableCrypto.Helios.Computational.TrusteeReachableSimulation
