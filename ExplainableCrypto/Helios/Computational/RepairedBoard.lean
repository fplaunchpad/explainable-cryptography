import ExplainableCrypto.Helios.Computational.StrongBallot
import ExplainableCrypto.Helios.Computational.Board
import ExplainableCrypto.Helios.Computational.Trustee

/-! BPW strong proofs and explicit/implicit ciphertext weeding. The historical
submission order and rejection/retained-board behavior are preserved. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

instance [DecidableEq F] [DecidableEq G] (hash : StatementHash F G) (g pk : G)
    {n : Nat} (b : Ballot F G n) : Decidable (b.StrongValid hash g pk) := by
  unfold Ballot.StrongValid Proof01.StrongValid Proof01.Valid Branch.Valid
  infer_instance

instance [DecidableEq G] {n : Nat} (b : Ballot F G n) (board : List (Ballot F G n)) :
    Decidable (b.ExpandedFreshFor board) := by
  unfold Ballot.ExpandedFreshFor
  infer_instance

def repairedSubmit [DecidableEq F] [DecidableEq G] (hash : StatementHash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    Decision × List (BoardEntry F G) :=
  if b.StrongValid hash g pk then
    if b.ExpandedFreshFor (board.map BoardEntry.ballot) then
      (.accepted, board ++ [⟨voter, b⟩])
    else (.reusedCiphertext, board)
  else (.invalidProof, board)

theorem repairedSubmit_accepted [DecidableEq F] [DecidableEq G] (hash : StatementHash F G)
    (g pk : G) (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (hv : b.StrongValid hash g pk) (hf : b.ExpandedFreshFor (board.map BoardEntry.ballot)) :
    repairedSubmit hash g pk voter board b = (.accepted, board ++ [⟨voter, b⟩]) := by
  simp [repairedSubmit, hv, hf]

theorem repairedSubmit_rejected_preserves_board [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (h : (repairedSubmit hash g pk voter board b).1 ≠ .accepted) :
    (repairedSubmit hash g pk voter board b).2 = board := by
  unfold repairedSubmit at h ⊢
  split <;> simp_all only
  split <;> simp_all

theorem repairedSubmit_proofReuse_rejected [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (target : Ballot F G 2)
    (ht : target ∈ board.map BoardEntry.ballot) (hv : target.StrongValid hash g pk)
    (e z w : F) :
    repairedSubmit hash g pk voter board (strongProofReuse hash g pk e z w target) =
      (.reusedCiphertext, board) := by
  have hn : ¬ (strongProofReuse hash g pk e z w target).ExpandedFreshFor
      (board.map BoardEntry.ballot) :=
    proofReuse_not_expanded_fresh (hash g pk (0, 0)) g pk e z w target _ ht
  have hp := strongProofReuse_valid hash g pk e z w target hv
  unfold repairedSubmit
  rw [if_pos hp, if_neg hn]

def repairedCastHonestPair [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) : (Decision × Decision) × List (BoardEntry F G) :=
  let first := repairedSubmit hash g pk 0 [] (strongHonestBallot hash g pk vote aliceCoins)
  let second := repairedSubmit hash g pk 1 first.2 (strongHonestBallot hash g pk (!vote) bobCoins)
  ((first.1, second.1), second.2)

theorem repairedCastHonestPair_eq [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g pk : G) (hg : Function.Injective (fun r : F => r • g))
    (vote : Bool) (aliceCoins bobCoins : HonestCoins F)
    (hc : ∀ i j, bobCoins.coveredNonce i ≠ aliceCoins.coveredNonce j) :
    repairedCastHonestPair hash g pk vote aliceCoins bobCoins = ((.accepted, .accepted),
      [⟨0, strongHonestBallot hash g pk vote aliceCoins⟩,
        ⟨1, strongHonestBallot hash g pk (!vote) bobCoins⟩]) := by
  have hf := strongHonestBallot_expanded_fresh hash g pk hg aliceCoins bobCoins vote (!vote) hc
  simp only [repairedCastHonestPair,
    repairedSubmit_accepted hash g pk 0 [] _ (strongHonestBallot_valid _ _ _ _ _)
      (by simp [Ballot.ExpandedFreshFor]), List.nil_append]
  rw [repairedSubmit_accepted hash g pk 1 _ _ (strongHonestBallot_valid _ _ _ _ _)
    (by simpa using hf)]
  rfl

theorem strongHonestPair_tally (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) (candidate : Fin 2) :
    boardTally [⟨0, strongHonestBallot hash g pk vote aliceCoins⟩,
      ⟨1, strongHonestBallot hash g pk (!vote) bobCoins⟩] candidate =
      encryptWith g pk (aliceCoins.nonce candidate + bobCoins.nonce candidate)
        (if candidate = 0 then 1 else 0) := by
  fin_cases candidate <;> cases vote <;>
    simp [boardTally, strongHonestBallot, encryptWith_add, voteScalar]

theorem repairedHonestPair_decrypts [DecidableEq F] [DecidableEq G]
    (hash : StatementHash F G) (g : G) (secret : F)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F)
    (hc : ∀ i j, bobCoins.coveredNonce i ≠ aliceCoins.coveredNonce j) (candidate : Fin 2) :
    let ct := boardTally (repairedCastHonestPair hash g (secret • g) vote aliceCoins bobCoins).2 candidate
    decryptWithPartial ct (partialDecrypt secret ct) =
      (if candidate = 0 then (1 : F) else 0) • g := by
  rw [repairedCastHonestPair_eq hash g (secret • g) hg vote aliceCoins bobCoins hc]
  simp only [strongHonestPair_tally]
  exact decryptWithPartial_correct _ _ _ _

#print axioms repairedSubmit_proofReuse_rejected
#print axioms repairedCastHonestPair_eq
#print axioms repairedHonestPair_decrypts

end ExplainableCrypto.Helios.Computational
