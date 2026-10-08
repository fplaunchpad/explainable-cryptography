import ExplainableCrypto.Helios.Computational.HonestBallot

/-! Concrete ballot submission. The three-voter experiment authenticates one
scheduled submission per eligible identity. Invalid submissions leave the board
unchanged; the election can still process later submissions and publish a tally. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

instance [DecidableEq F] [DecidableEq G] (hash : Hash F G) (g pk : G)
    {n : Nat} (b : Ballot F G n) : Decidable (b.Valid hash g pk) := by
  unfold Ballot.Valid Proof01.Valid Branch.Valid
  infer_instance

instance [DecidableEq G] {n : Nat} (b : Ballot F G n) (board : List (Ballot F G n)) :
    Decidable (b.FreshFor board) := by
  unfold Ballot.FreshFor
  infer_instance

structure BoardEntry (F G : Type) where
  voter : Fin 3
  ballot : Ballot F G 2

inductive Decision | accepted | invalidProof | reusedCiphertext
  deriving DecidableEq, Repr

def submit [DecidableEq F] [DecidableEq G] (hash : Hash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    Decision × List (BoardEntry F G) :=
  if b.Valid hash g pk then
    if b.FreshFor (board.map BoardEntry.ballot) then
      (.accepted, board ++ [⟨voter, b⟩])
    else (.reusedCiphertext, board)
  else (.invalidProof, board)

theorem submit_accepted [DecidableEq F] [DecidableEq G] (hash : Hash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (h : b.Accepted hash g pk (board.map BoardEntry.ballot)) :
    submit hash g pk voter board b = (.accepted, board ++ [⟨voter, b⟩]) := by
  simp [submit, h.1, h.2]

theorem submit_rejected_preserves_board [DecidableEq F] [DecidableEq G]
    (hash : Hash F G) (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (h : (submit hash g pk voter board b).1 ≠ .accepted) :
    (submit hash g pk voter board b).2 = board := by
  unfold submit at h ⊢
  split <;> simp_all only
  split <;> simp_all

def castHonestPair [DecidableEq F] [DecidableEq G] (hash : Hash F G) (g pk : G)
    (vote : Bool) (left right : HonestCoins F) :
    (Decision × Decision) × List (BoardEntry F G) :=
  let first := submit hash g pk 0 [] (honestBallot hash g pk vote left)
  let second := submit hash g pk 1 first.2 (honestBallot hash g pk (!vote) right)
  ((first.1, second.1), second.2)

theorem castHonestPair_eq [DecidableEq F] [DecidableEq G] (hash : Hash F G) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g))
    (vote : Bool) (left right : HonestCoins F) (hc : CollisionFree left right) :
    castHonestPair hash g pk vote left right = ((.accepted, .accepted),
      [⟨0, honestBallot hash g pk vote left⟩, ⟨1, honestBallot hash g pk (!vote) right⟩]) := by
  have hfirst : (honestBallot hash g pk vote left).Accepted hash g pk [] :=
    ⟨honestBallot_valid _ _ _ _ _, by simp [Ballot.FreshFor]⟩
  have hsecond : (honestBallot hash g pk (!vote) right).Accepted hash g pk
      [honestBallot hash g pk vote left] :=
    ⟨honestBallot_valid _ _ _ _ _, honestBallot_fresh hash g pk hg left right _ _ hc.1⟩
  simp only [castHonestPair, submit_accepted hash g pk 0 [] _ hfirst, List.nil_append]
  rw [submit_accepted hash g pk 1 _ _ (by simpa using hsecond)]
  rfl

def boardTally (board : List (BoardEntry F G)) (candidate : Fin 2) : Ciphertext G :=
  (board.map (fun entry => entry.ballot.ciphertext candidate)).sum

theorem proofReuse_tally_first (hash : Hash F G) (g pk : G) (vote : Bool)
    (left right : HonestCoins F) (e z w : F) :
    boardTally [⟨0, honestBallot hash g pk vote left⟩,
      ⟨1, honestBallot hash g pk (!vote) right⟩,
      ⟨2, proofReuse hash g pk e z w (honestBallot hash g pk vote left)⟩] 0 =
    encryptWith g pk (left.nonce 0 + (right.nonce 0 + (left.nonce 0 + left.nonce 1)))
      (1 + voteScalar vote) := by
  simp only [boardTally, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, proofReuse, Fin.cases_zero, honestBallot_aggregate]
  change encryptWith g pk (left.nonce 0) (voteScalar vote) +
    (encryptWith g pk (right.nonce 0) (voteScalar (!vote)) +
      encryptWith g pk (left.nonce 0 + left.nonce 1) (voteScalar vote)) = _
  rw [encryptWith_add, encryptWith_add]
  cases vote <;> simp [voteScalar]

#print axioms submit_rejected_preserves_board
#print axioms castHonestPair_eq
#print axioms proofReuse_tally_first

end ExplainableCrypto.Helios.Computational
