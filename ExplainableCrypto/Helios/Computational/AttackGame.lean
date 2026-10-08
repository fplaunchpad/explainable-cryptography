import ExplainableCrypto.Helios.Computational.Board
import ExplainableCrypto.Helios.Computational.Trustee
import ExplainableCrypto.Helios.Computational.HonestSampling

/-! The concrete three-voter attack experiment, with one honest trustee.
The public transcript contains setup and key proof, accepted identified ballots,
decisions, the attacker's submission, encrypted tally, decryption shares/proofs
and bounded tally decoding. Only the private execution receives the secret key
and honest coins. Rejection retains the accepted board and tallying continues.
-/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

structure PublicParameters (F G : Type) where
  generator : G
  publicKey : G
  trusteeKeyProof : SchnorrProof F G
  candidates : List Nat := [0, 1]
  eligibleVoters : List (Fin 3) := [0, 1, 2]

structure CryptoHashes (F G : Type) where
  ballot : Hash F G
  key : G → F
  decryption : (G × G) → F
  fingerprint : PublicParameters F G → Nat

structure PublicPrefix (F G : Type) where
  parameters : PublicParameters F G
  fingerprint : Nat
  honestDecisions : Decision × Decision
  board : List (BoardEntry F G)

structure PublicResult (F G : Type) where
  beforeTally : PublicPrefix F G
  submission : Ballot F G 2
  decision : Decision
  board : List (BoardEntry F G)
  encryptedTally : Fin 2 → Ciphertext G
  decryptionShares : Fin 2 → G
  decryptionProofs : Fin 2 → SchnorrProof F (G × G)
  decodedTally : Fin 2 → Option Nat

def decodeBounded [DecidableEq G] (g : G) (bound : Nat) (message : G) : Option Nat :=
  (List.range (bound + 1)).find? (fun value => decide ((value : F) • g = message))

def makePrefix [DecidableEq F] [DecidableEq G] (hashes : CryptoHashes F G) (g : G)
    (secret keyNonce : F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) : PublicPrefix F G :=
  let parameters : PublicParameters F G :=
    ⟨g, secret • g, schnorrProof hashes.key g secret keyNonce, [0, 1], [0, 1, 2]⟩
  let cast := castHonestPair hashes.ballot g (secret • g) vote aliceCoins bobCoins
  ⟨parameters, hashes.fingerprint parameters, cast.1, cast.2⟩

/-- A total public algorithm; the first honest ballot is always present in
the reached experiment, so the empty-board fallback is never needed there. -/
def proofReuseSubmission (hashes : CryptoHashes F G) (beforeTally : PublicPrefix F G) : Ballot F G 2 :=
  let g := beforeTally.parameters.generator
  let pk := beforeTally.parameters.publicKey
  match beforeTally.board with
  | [] => ⟨fun _ => (0, 0), fun _ => neutralProof hashes.ballot g pk 1 1 1,
      neutralProof hashes.ballot g pk 1 1 1⟩
  | first :: _ => proofReuse hashes.ballot g pk 1 1 1 first.ballot

def finishElection [DecidableEq F] [DecidableEq G] (hashes : CryptoHashes F G)
    (secret : F) (decryptionNonces : Fin 2 → F) (beforeTally : PublicPrefix F G)
    (submission : Ballot F G 2) : PublicResult F G :=
  let g := beforeTally.parameters.generator
  let cast := submit hashes.ballot g beforeTally.parameters.publicKey 2 beforeTally.board submission
  let encrypted := boardTally cast.2
  let shares := fun j => partialDecrypt secret (encrypted j)
  ⟨beforeTally, submission, cast.1, cast.2, encrypted, shares,
    fun j => partialProof hashes.decryption g secret (decryptionNonces j) (encrypted j),
    fun j => decodeBounded (F := F) g cast.2.length (decryptWithPartial (encrypted j) (shares j))⟩

def publicDecrypted (view : PublicResult F G) (candidate : Fin 2) : G :=
  decryptWithPartial (view.encryptedTally candidate) (view.decryptionShares candidate)

def attackDistinguisher [DecidableEq G] (view : PublicResult F G) : Bool :=
  decide (publicDecrypted view 0 = (2 : F) • view.beforeTally.parameters.generator)

def executeAttack [DecidableEq F] [DecidableEq G] (hashes : CryptoHashes F G) (g : G)
    (secret keyNonce : F) (decryptionNonces : Fin 2 → F) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) : PublicResult F G :=
  let beforeTally := makePrefix hashes g secret keyNonce vote aliceCoins bobCoins
  finishElection hashes secret decryptionNonces beforeTally (proofReuseSubmission hashes beforeTally)

theorem executeAttack_on_good [DecidableEq F] [DecidableEq G] (hashes : CryptoHashes F G)
    (g : G) (hg : Function.Injective (fun r : F => r • g)) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F)
    (hl : ∀ i, aliceCoins.nonce i ≠ 0) (hr : ∀ i, bobCoins.nonce i ≠ 0)
    (hc : CollisionFree aliceCoins bobCoins) :
    (executeAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins).decision = .accepted ∧
      publicDecrypted (executeAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins) 0 =
        (1 + voteScalar vote : F) • g := by
  have hprefix := castHonestPair_eq hashes.ballot g (secret • g) hg vote aliceCoins bobCoins hc
  have hvalid := proofReuse_valid hashes.ballot g (secret • g) 1 1 1
    (honestBallot hashes.ballot g (secret • g) vote aliceCoins)
    (honestBallot_valid _ _ _ _ _)
  have hfresh := proofReuse_honest_fresh hashes.ballot g (secret • g) hg aliceCoins bobCoins vote (!vote)
    1 1 1 hl hr hc
  have hcast := submit_accepted hashes.ballot g (secret • g) 2
    [⟨0, honestBallot hashes.ballot g (secret • g) vote aliceCoins⟩,
      ⟨1, honestBallot hashes.ballot g (secret • g) (!vote) bobCoins⟩]
    (proofReuse hashes.ballot g (secret • g) 1 1 1
      (honestBallot hashes.ballot g (secret • g) vote aliceCoins))
    (by exact ⟨hvalid, by simpa using hfresh⟩)
  simp only [executeAttack, makePrefix, hprefix, proofReuseSubmission, finishElection, hcast,
    List.cons_append, List.nil_append, publicDecrypted, proofReuse_tally_first]
  exact ⟨trivial, decryptWithPartial_correct _ _ _ _⟩

theorem attackDistinguisher_on_good [DecidableEq F] [DecidableEq G]
    (hashes : CryptoHashes F G) (g : G) (hg : Function.Injective (fun r : F => r • g))
    (secret keyNonce : F) (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F)
    (hl : ∀ i, aliceCoins.nonce i ≠ 0) (hr : ∀ i, bobCoins.nonce i ≠ 0) (hc : CollisionFree aliceCoins bobCoins) :
    attackDistinguisher (executeAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins) = vote := by
  have ht := (executeAttack_on_good hashes g hg secret keyNonce decryptionNonces vote aliceCoins bobCoins hl hr hc).2
  have h12 : (1 : F) ≠ 2 := by
    intro he
    have he' : (1 : F) + 0 = 1 + 1 :=
      (add_zero _).trans (he.trans one_add_one_eq_two.symm)
    exact zero_ne_one (add_left_cancel he')
  have hgen : (1 : F) • g ≠ (2 : F) • g := fun he => h12 (hg he)
  unfold attackDistinguisher
  rw [ht]
  change decide ((1 + voteScalar vote : F) • g = (2 : F) • g) = vote
  cases vote
  · simpa only [voteScalar, Bool.false_eq_true, ↓reduceIte, add_zero, decide_eq_false_iff_not] using hgen
  · simp only [voteScalar, ↓reduceIte, one_add_one_eq_two, decide_true]

theorem executeAttack_key_proof_valid [DecidableEq F] [DecidableEq G]
    (hashes : CryptoHashes F G) (g : G) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    let view := executeAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins
    view.beforeTally.parameters.trusteeKeyProof.Valid hashes.key g
      view.beforeTally.parameters.publicKey :=
  schnorrProof_valid hashes.key g secret keyNonce

theorem executeAttack_decryption_proofs_valid [DecidableEq F] [DecidableEq G]
    (hashes : CryptoHashes F G) (g : G) (secret keyNonce : F)
    (decryptionNonces : Fin 2 → F) (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    let view := executeAttack hashes g secret keyNonce decryptionNonces vote aliceCoins bobCoins
    ∀ candidate, (view.decryptionProofs candidate).Valid hashes.decryption
      (g, (view.encryptedTally candidate).1)
      (view.beforeTally.parameters.publicKey, view.decryptionShares candidate) := by
  intro view candidate
  exact partialProof_valid hashes.decryption g secret (decryptionNonces candidate) _

open OracleComp

noncomputable def attackWorld [Fintype F] [DecidableEq F] [DecidableEq G]
    (hashes : CryptoHashes F G) (g : G) (vote : Bool) : ProbComp (PublicResult F G) := do
  let secret ← sampleNonzero F
  let keyNonce ← sampleNonzero F
  let decryptionNonces ← drawNoncePair F
  let pair ← drawHonestPair F
  pure (executeAttack hashes g secret keyNonce ![decryptionNonces.1, decryptionNonces.2]
    vote pair.1 pair.2)

#print axioms executeAttack_key_proof_valid
#print axioms executeAttack_decryption_proofs_valid
#print axioms executeAttack_on_good
#print axioms attackDistinguisher_on_good

end ExplainableCrypto.Helios.Computational
