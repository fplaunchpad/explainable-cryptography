import ExplainableCrypto.Helios.Computational.RepairedBoard
import ExplainableCrypto.Helios.Computational.AttackGame

/-! The selected concrete repair in the same public execution interface. Hash
inputs now contain the statements for ballot, key and partial-decryption proofs.
The fixed three-voter/one-honest-trustee scope and public rejection are retained.
This is an execution/correctness layer, not a computational privacy reduction. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

structure StrongCryptoHashes (F G : Type) where
  ballot : StatementHash F G
  key : G → G → G → F
  decryption : G → G → Ciphertext G → G → (G × G) → F
  fingerprint : PublicParameters F G → Nat

def strongKeyProof (hashes : StrongCryptoHashes F G) (g : G) (secret nonce : F) :
    SchnorrProof F G := schnorrProof (hashes.key g (secret • g)) g secret nonce

def strongPartialProof (hashes : StrongCryptoHashes F G) (g : G) (secret nonce : F)
    (ct : Ciphertext G) : SchnorrProof F (G × G) :=
  partialProof (hashes.decryption g (secret • g) ct (partialDecrypt secret ct)) g secret nonce ct

def makeRepairedPrefix [DecidableEq F] [DecidableEq G] (hashes : StrongCryptoHashes F G)
    (g : G) (secret keyNonce : F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    PublicPrefix F G :=
  let parameters : PublicParameters F G :=
    ⟨g, secret • g, strongKeyProof hashes g secret keyNonce, [0, 1], [0, 1, 2]⟩
  let cast := repairedCastHonestPair hashes.ballot g (secret • g) vote aliceCoins bobCoins
  ⟨parameters, hashes.fingerprint parameters, cast.1, cast.2⟩

def repairedProofReuseSubmission (hashes : StrongCryptoHashes F G)
    (beforeTally : PublicPrefix F G) : Ballot F G 2 :=
  let g := beforeTally.parameters.generator
  let pk := beforeTally.parameters.publicKey
  match beforeTally.board with
  | [] => ⟨fun _ => (0, 0), fun _ => neutralProof (hashes.ballot g pk (0, 0)) g pk 1 1 1,
      neutralProof (hashes.ballot g pk (0, 0)) g pk 1 1 1⟩
  | first :: _ => strongProofReuse hashes.ballot g pk 1 1 1 first.ballot

def finishRepairedElection [DecidableEq F] [DecidableEq G]
    (hashes : StrongCryptoHashes F G) (secret : F) (decryptionNonces : Fin 2 → F)
    (beforeTally : PublicPrefix F G) (submission : Ballot F G 2) : PublicResult F G :=
  let g := beforeTally.parameters.generator
  let cast := repairedSubmit hashes.ballot g beforeTally.parameters.publicKey 2 beforeTally.board submission
  let encrypted := boardTally cast.2
  let shares := fun j => partialDecrypt secret (encrypted j)
  ⟨beforeTally, submission, cast.1, cast.2, encrypted, shares,
    fun j => strongPartialProof hashes g secret (decryptionNonces j) (encrypted j),
    fun j => decodeBounded (F := F) g cast.2.length (decryptWithPartial (encrypted j) (shares j))⟩

def executeRepairedAttack [DecidableEq F] [DecidableEq G] (hashes : StrongCryptoHashes F G)
    (g : G) (secret keyNonce : F) (decryptionNonces : Fin 2 → F) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) : PublicResult F G :=
  let beforeTally := makeRepairedPrefix hashes g secret keyNonce vote aliceCoins bobCoins
  finishRepairedElection hashes secret decryptionNonces beforeTally
    (repairedProofReuseSubmission hashes beforeTally)

theorem repairedCastHonestPair_first [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g pk : G) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    ∃ rest, (repairedCastHonestPair hash g pk vote aliceCoins bobCoins).2 =
      ⟨0, strongHonestBallot hash g pk vote aliceCoins⟩ :: rest := by
  simp only [repairedCastHonestPair,
    repairedSubmit_accepted hash g pk 0 [] _ (strongHonestBallot_valid _ _ _ _ _)
      (by simp [Ballot.ExpandedFreshFor]), List.nil_append]
  unfold repairedSubmit
  split
  · split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem executeRepairedAttack_rejected [DecidableEq F] [DecidableEq G]
    (hashes : StrongCryptoHashes F G) (g : G) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    (executeRepairedAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins).decision =
      .reusedCiphertext := by
  obtain ⟨rest, hb⟩ := repairedCastHonestPair_first hashes.ballot g (secret • g) vote aliceCoins bobCoins
  simp only [executeRepairedAttack, makeRepairedPrefix, repairedProofReuseSubmission, hb,
    finishRepairedElection]
  rw [repairedSubmit_proofReuse_rejected hashes.ballot g (secret • g) 2 _ _
    (by simp) (strongHonestBallot_valid _ _ _ _ _) 1 1 1]

theorem executeRepairedAttack_key_proof_valid [DecidableEq F] [DecidableEq G]
    (hashes : StrongCryptoHashes F G) (g : G) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    let view := executeRepairedAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins
    view.beforeTally.parameters.trusteeKeyProof.Valid
      (hashes.key g view.beforeTally.parameters.publicKey) g view.beforeTally.parameters.publicKey :=
  schnorrProof_valid _ g secret keyNonce

theorem executeRepairedAttack_decryption_proofs_valid [DecidableEq F] [DecidableEq G]
    (hashes : StrongCryptoHashes F G) (g : G) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    let view := executeRepairedAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins
    ∀ candidate, (view.decryptionProofs candidate).Valid
      (hashes.decryption g view.beforeTally.parameters.publicKey
        (view.encryptedTally candidate) (view.decryptionShares candidate))
      (g, (view.encryptedTally candidate).1)
      (view.beforeTally.parameters.publicKey, view.decryptionShares candidate) := by
  intro view candidate
  exact partialProof_valid _ g secret (decryptionNonces candidate) _

#print axioms executeRepairedAttack_rejected
#print axioms executeRepairedAttack_key_proof_valid
#print axioms executeRepairedAttack_decryption_proofs_valid

end ExplainableCrypto.Helios.Computational
