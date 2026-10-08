import ExplainableCrypto.Helios.Computational.ElectionExtraction

/-! Move independent private trustee draws to their use points in the actual
full election. Equalities concern output distributions including final caches;
they do not assert equality of source query trees or extractor replay paths. -/
namespace ExplainableCrypto.Helios.Computational.ElectionNonceSchedule
open OracleComp OracleSpec ElectionOracle ElectionCache
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual submission and publication, with a fresh historical nonce drawn
immediately before each of the two original decryption proof algorithms. -/
noncomputable def finish (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) : Comp F G (PublicResult F G) := do
  let g := before.parameters.generator
  let cast ← liftBallot (repairedSubmitOracle g before.parameters.publicKey 2 before.board submission)
  let encrypted := boardTally cast.2
  let shares := fun j => partialDecrypt secret (encrypted j)
  let r0 ← liftProb (sampleNonzero F)
  let proof0 ← partialWithCoins g secret r0 (encrypted 0)
  let r1 ← liftProb (sampleNonzero F)
  let proof1 ← partialWithCoins g secret r1 (encrypted 1)
  pure ⟨before,submission,cast.1,cast.2,encrypted,shares,![proof0,proof1],
    fun j => decodeBounded (F := F) g cast.2.length (decryptWithPartial (encrypted j) (shares j))⟩

/-- Both independent decryption nonces can be delayed past actual submission
validation. The arbitrary continuation retains every later observation/query. -/
theorem finish_eq {A : Type} (secret : F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (next : PublicResult F G → Comp F G A) (cache : Cache F G) :
    𝒮[run (do let rs ← liftProb (drawNoncePair F)
               let view ← finishWithCoins secret ![rs.1,rs.2] before submission
               next view) cache] =
      𝒮[run (finish secret before submission >>= next) cache] := by
  simp only [finishWithCoins,finish,bind_assoc,run_bind,run_liftProb,bind_map_left,pure_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro cast
  simp only [drawNoncePair,bind_assoc,pure_bind,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  apply evalSPMF_bind_congr'
  intro r0
  rw [evalSPMF_bind_bind_swap]

/-- The full source with key/decryption nonces sampled at their proof-use
points. Honest coin records stay private; the actual prefix and attacker
callbacks are unchanged. -/
noncomputable def world {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (adversary : Adversary F G State) (vote : Bool) :
    Comp F G (PublicResult F G × Bool) := do
  let secret ← liftProb (sampleNonzero F)
  let pair ← liftProb (drawHonestPair F)
  let keyNonce ← liftProb (sampleNonzero F)
  let before ← prefixWithCoins fingerprint g secret keyNonce vote pair.1 pair.2
  let (submission,saved) ← adversary.castBallot before
  let view ← finish secret before submission
  let guess ← adversary.guessVote saved view
  pure (view,guess)

/-- Delaying the original private nonce draws preserves the complete actual
world, including all guessing queries, the public result and final full cache. -/
theorem world_eq {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (adversary : Adversary F G State) (vote : Bool) (cache : Cache F G) :
    𝒮[run (ElectionExtraction.worldSource fingerprint g adversary vote) cache] =
      𝒮[run (world fingerprint g adversary vote) cache] := by
  simp only [ElectionExtraction.worldSource,samplePrefix,world,bind_assoc,pure_bind,
    run_liftProb_bind]
  apply evalSPMF_bind_congr'
  intro secret
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext keyNonce
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro pair
  apply evalSPMF_bind_congr'
  intro keyNonce
  simp only [run_bind]
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro before
  conv_lhs => rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro cast
  simpa only [run_bind,run_liftProb,bind_map_left] using finish_eq secret before.1 cast.1.1
    (fun view => do let guess ← adversary.guessVote cast.1.2 view; pure (view,guess)) cast.2

/-- Preparation retains its actual state and cache before the challenge. -/
noncomputable def prepared {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) :
    Comp F G (PublicResult F G × Bool) := do
  let initial ← prepare
  let vote ← liftProb (uniformSample Bool)
  let (view,guess) ← world fingerprint g (adversary initial) vote
  pure (view,decide (guess = vote))

/-- Exact real-source output/cache distribution after arbitrary pre-election
queries. Replaying either query tree is a separate operation. -/
theorem prepared_eq {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (cache : Cache F G) :
    𝒮[run (ElectionExtraction.preparedSource fingerprint g prepare adversary) cache] =
      𝒮[run (prepared fingerprint g prepare adversary) cache] := by
  simp only [ElectionExtraction.preparedSource,prepared,run_bind,run_liftProb,bind_map_left]
  apply evalSPMF_bind_congr'
  intro initial
  apply evalSPMF_bind_congr'
  intro vote
  simp only [evalSPMF_bind,world_eq]

/-- The original random-oracle game's winning-bit distribution is preserved.
This is a schedule correspondence, not an advantage or secrecy bound. -/
theorem winning_eq {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) :
    𝒮[randomGame fingerprint g prepare adversary] =
      𝒮[(fun out => out.1.2) <$> run (prepared fingerprint g prepare adversary) ∅] := by
  have h := evalSPMF_map_eq_of_evalSPMF_eq
    (prepared_eq fingerprint g prepare adversary ∅) (fun out => out.1.2)
  unfold randomGame
  change 𝒮[Prod.fst <$> run (preparedGame fingerprint g prepare adversary) (∅ : Cache F G)] = _
  rw [← ElectionExtraction.preparedSource_project]
  simpa only [run,simulateQ_map,StateT.run_map,Functor.map_map,Function.comp_def] using h

#print axioms finish_eq
#print axioms world_eq
#print axioms prepared_eq
#print axioms winning_eq
end ExplainableCrypto.Helios.Computational.ElectionNonceSchedule
