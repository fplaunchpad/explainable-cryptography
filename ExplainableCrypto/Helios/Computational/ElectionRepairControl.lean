import ExplainableCrypto.Helios.Computational.ElectionOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-! The original neutral-ciphertext/proof-reuse attack executed against the
repaired shared oracle. The result retains the entire public election record.
Probability-one rejection is a known-attack control, not ballot secrecy. -/
namespace ExplainableCrypto.Helios.Computational.ElectionOracle
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

/-- Construct the original submission, querying the neutral proof's full statement. -/
def repairedReuseSubmission (before : PublicPrefix F G) : Comp F G (Ballot F G 2) := do
  let g := before.parameters.generator
  let pk := before.parameters.publicKey
  let c ← ask (.ballot ⟨g, pk, (0, 0)⟩ ((g, pk), (g, pk + g)))
  pure (match before.board with
    | [] => ⟨fun _ => (0, 0), fun _ => neutralProof (fun _ => c) g pk 1 1 1,
        neutralProof (fun _ => c) g pk 1 1 1⟩
    | first :: _ => proofReuse (fun _ => c) g pk 1 1 1 first.ballot)

theorem repairedReuseSubmission_function (hashes : StrongCryptoHashes F G)
    (before : PublicPrefix F G) :
    simulateQ (functionImpl hashes) (repairedReuseSubmission before) =
      pure (repairedProofReuseSubmission hashes before) := by
  simp only [repairedReuseSubmission, simulateQ_bind, ask_function, pure_bind, simulateQ_pure]
  cases h : before.board <;>
    simp [repairedProofReuseSubmission, h, strongProofReuse, proofReuse, neutralProof]

variable [DecidableEq F] [DecidableEq G]

def repairedAttackWithCoins (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret keyNonce : F) (nonces : Fin 2 → F) (vote : Bool)
    (alice bob : HonestCoins F) : Comp F G (PublicResult F G) := do
  let before ← prefixWithCoins fingerprint g secret keyNonce vote alice bob
  let submission ← repairedReuseSubmission before
  finishWithCoins secret nonces before submission

/-- Equality of all public fields under every fixed hash interpretation. -/
theorem repairedAttackWithCoins_function (hashes : StrongCryptoHashes F G) (g : G)
    (secret keyNonce : F) (nonces : Fin 2 → F) (vote : Bool) (alice bob : HonestCoins F) :
    simulateQ (functionImpl hashes)
      (repairedAttackWithCoins hashes.fingerprint g secret keyNonce nonces vote alice bob) =
      pure (executeRepairedAttack hashes g secret keyNonce nonces vote alice bob) := by
  simp [repairedAttackWithCoins, prefix_function, repairedReuseSubmission_function,
    finish_function, executeRepairedAttack]

private def answerHashes (fingerprint : PublicParameters F G → Nat)
    (f : QueryImpl (HashSpec F G) Id) : StrongCryptoHashes F G where
  ballot g pk ct pc := f (.ballot ⟨g, pk, ct⟩ pc)
  key g pk pc := f (.key g pk pc)
  decryption g pk ct share pc := f (.decryption g pk ct share pc)
  fingerprint := fingerprint

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
private theorem answer_function (fingerprint : PublicParameters F G → Nat)
    (f : QueryImpl (HashSpec F G) Id) :
    functionImpl (answerHashes fingerprint f) = unifFwdAnswerImpl f := by
  funext t
  cases t with
  | inl n => rfl
  | inr k => cases k <;> rfl

variable [SampleableType F]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
private theorem run_probability_one {A : Type} (oa : Comp F G A)
    (fingerprint : PublicParameters F G → Nat) (cache : Cache F G) (p : A → Prop)
    (h : ∀ hashes : StrongCryptoHashes F G, hashes.fingerprint = fingerprint →
      Pr[p | simulateQ (functionImpl hashes) oa] = 1) :
    Pr[fun out => p out.1 | run oa cache] = 1 := by
  apply (probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff oa cache p).mpr
  intro f _
  rw [← answer_function fingerprint f]
  exact h (answerHashes fingerprint f) rfl

/-- Every initial cache and every coin tuple gives the original reuse rejection. -/
theorem repairedAttackWithCoins_rejected (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret keyNonce : F) (nonces : Fin 2 → F) (vote : Bool) (alice bob : HonestCoins F)
    (cache : Cache F G) :
    Pr[fun out => out.1.decision = .reusedCiphertext |
      run (repairedAttackWithCoins fingerprint g secret keyNonce nonces vote alice bob) cache] = 1 := by
  apply run_probability_one _ fingerprint cache (fun view : PublicResult F G => view.decision = .reusedCiphertext)
  intro hashes hf
  rw [← hf, repairedAttackWithCoins_function]
  simp [executeRepairedAttack_rejected]

variable [Fintype F]

/-- The original nonzero sampling schedule, with the shared oracle retained. -/
noncomputable def repairedAttackWorld (fingerprint : PublicParameters F G → Nat) (g : G)
    (vote : Bool) : Comp F G (PublicResult F G) := do
  let secret ← liftProb (sampleNonzero F)
  let keyNonce ← liftProb (sampleNonzero F)
  let nonces ← liftProb (drawNoncePair F)
  let pair ← liftProb (drawHonestPair F)
  repairedAttackWithCoins fingerprint g secret keyNonce ![nonces.1, nonces.2] vote pair.1 pair.2

omit [SampleableType F] in
theorem repairedAttackWorld_function (hashes : StrongCryptoHashes F G) (g : G) (vote : Bool) :
    simulateQ (functionImpl hashes) (repairedAttackWorld hashes.fingerprint g vote) =
      Computational.repairedAttackWorld hashes g vote := by
  simp [repairedAttackWorld, liftProb_function, repairedAttackWithCoins_function,
    Computational.repairedAttackWorld]

/-- Sampling keeps rejection probability one; no collision event is conditioned away. -/
theorem repairedAttackWorld_rejected (fingerprint : PublicParameters F G → Nat) (g : G)
    (vote : Bool) (cache : Cache F G) :
    Pr[fun out => out.1.decision = .reusedCiphertext |
      run (repairedAttackWorld fingerprint g vote) cache] = 1 := by
  apply run_probability_one _ fingerprint cache (fun view : PublicResult F G => view.decision = .reusedCiphertext)
  intro hashes hf
  rw [← hf, repairedAttackWorld_function]
  exact repairedAttackWorld_rejection_probability hashes g vote

end ExplainableCrypto.Helios.Computational.ElectionOracle
