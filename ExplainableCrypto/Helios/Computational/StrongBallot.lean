import ExplainableCrypto.Helios.Computational.HonestBallot

/-! BPW section 5: hash generator, public key and the ciphertext statement as
well as commitments. The arithmetic proof and transcript format are reused.
Correctness here quantifies over every hash; random-oracle security is separate. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

abbrev StatementHash (F G : Type) := G → G → Ciphertext G → Hash F G

def Proof01.StrongValid (hash : StatementHash F G) (g pk : G) (ct : Ciphertext G)
    (p : Proof01 F G) : Prop := p.Valid (hash g pk ct) g pk ct

def strongProveVote (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (r w e z : F) : Proof01 F G :=
  proveVote (hash g pk (encryptWith g pk r (voteScalar vote))) g pk vote r w e z

theorem strongProveVote_valid (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (r w e z : F) :
    (strongProveVote hash g pk vote r w e z).StrongValid hash g pk
      (encryptWith g pk r (voteScalar vote)) :=
  proveVote_valid _ _ _ _ _ _ _ _

def Ballot.StrongValid {n : Nat} (hash : StatementHash F G) (g pk : G)
    (b : Ballot F G n) : Prop :=
  (∀ i, (b.proof i).StrongValid hash g pk (b.ciphertext i)) ∧
    b.overall.StrongValid hash g pk b.aggregate

/-- `none` is the implicit aggregate; `some i` is an explicit component. -/
def Ballot.coveredCiphertext {n : Nat} (b : Ballot F G n) : Option (Fin n) → Ciphertext G
  | none => b.aggregate
  | some i => b.ciphertext i

def Ballot.ExpandedFreshFor {n : Nat} (b : Ballot F G n)
    (board : List (Ballot F G n)) : Prop :=
  ∀ old ∈ board, ∀ i j, b.coveredCiphertext i ≠ old.coveredCiphertext j

omit [Field F] [Module F G] in
theorem Ballot.ExpandedFreshFor.component_fresh {n : Nat} {b : Ballot F G n}
    {board : List (Ballot F G n)} (h : b.ExpandedFreshFor board) : b.FreshFor board :=
  fun old ho i j => h old ho (some i) (some j)

omit [Field F] [Module F G] in
theorem copied_aggregate_not_expanded_fresh {n : Nat} {target b : Ballot F G n}
    {board : List (Ballot F G n)} (ht : target ∈ board) (i : Fin n)
    (hi : b.ciphertext i = target.aggregate) : ¬ b.ExpandedFreshFor board :=
  fun h => h target ht (some i) none hi

theorem proofReuse_not_expanded_fresh {n : Nat} (hash : Hash F G) (g pk : G)
    (e z w : F) (target : Ballot F G (n + 1)) (board : List (Ballot F G (n + 1)))
    (ht : target ∈ board) :
    ¬ (proofReuse hash g pk e z w target).ExpandedFreshFor board :=
  copied_aggregate_not_expanded_fresh ht 0 rfl

def strongHonestBallot (hash : StatementHash F G) (g pk : G) (vote : Bool)
    (coins : HonestCoins F) : Ballot F G 2 where
  ciphertext := ![encryptWith g pk (coins.nonce 0) (voteScalar vote),
    encryptWith g pk (coins.nonce 1) 0]
  proof := ![strongProveVote hash g pk vote (coins.nonce 0)
    (coins.witness 0) (coins.challenge 0) (coins.response 0),
    strongProveVote hash g pk false (coins.nonce 1)
      (coins.witness 1) (coins.challenge 1) (coins.response 1)]
  overall := strongProveVote hash g pk vote (coins.nonce 0 + coins.nonce 1)
    (coins.witness 2) (coins.challenge 2) (coins.response 2)

theorem strongHonestBallot_aggregate (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (coins : HonestCoins F) :
    (strongHonestBallot hash g pk vote coins).aggregate =
      encryptWith g pk (coins.nonce 0 + coins.nonce 1) (voteScalar vote) := by
  simp [Ballot.aggregate, strongHonestBallot, Fin.sum_univ_two, encryptWith_add]

theorem strongHonestBallot_valid (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (coins : HonestCoins F) :
    (strongHonestBallot hash g pk vote coins).StrongValid hash g pk := by
  constructor
  · intro i
    fin_cases i
    · exact strongProveVote_valid hash g pk vote _ _ _ _
    · exact strongProveVote_valid hash g pk false _ _ _ _
  · rw [strongHonestBallot_aggregate]
    exact strongProveVote_valid hash g pk vote _ _ _ _

def HonestCoins.coveredNonce (coins : HonestCoins F) : Option (Fin 2) → F
  | none => coins.nonce 0 + coins.nonce 1
  | some i => coins.nonce i

theorem strongHonestBallot_covered_nonce (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (coins : HonestCoins F) (i : Option (Fin 2)) :
    ((strongHonestBallot hash g pk vote coins).coveredCiphertext i).1 =
      coins.coveredNonce i • g := by
  cases i with
  | none => simp [Ballot.coveredCiphertext, strongHonestBallot_aggregate,
      HonestCoins.coveredNonce, encryptWith]
  | some i => fin_cases i <;> rfl

theorem strongHonestBallot_expanded_fresh (hash : StatementHash F G) (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (aliceCoins bobCoins : HonestCoins F)
    (v w : Bool) (h : ∀ i j, bobCoins.coveredNonce i ≠ aliceCoins.coveredNonce j) :
    (strongHonestBallot hash g pk w bobCoins).ExpandedFreshFor
      [strongHonestBallot hash g pk v aliceCoins] := by
  intro old ho i j heq
  simp only [List.mem_singleton] at ho
  subst old
  apply h i j
  apply hg
  have he := congrArg Prod.fst heq
  simpa only [strongHonestBallot_covered_nonce] using he

/-- Strong Fiat–Shamir alone still permits this exact proof reuse: its statement
is the same aggregate ciphertext. Expanded weeding is independently necessary. -/
def strongProofReuse {n : Nat} (hash : StatementHash F G) (g pk : G) (e z w : F)
    (target : Ballot F G (n + 1)) : Ballot F G (n + 1) :=
  proofReuse (hash g pk (0, 0)) g pk e z w target

theorem strongProofReuse_valid {n : Nat} (hash : StatementHash F G) (g pk : G)
    (e z w : F) (target : Ballot F G (n + 1)) (ht : target.StrongValid hash g pk) :
    (strongProofReuse hash g pk e z w target).StrongValid hash g pk := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ht.2
    · exact neutralProof_valid (hash g pk (0, 0)) g pk e z w
  · unfold strongProofReuse
    rw [proofReuse_aggregate]
    exact ht.2

#print axioms strongProofReuse_valid
#print axioms strongHonestBallot_valid
#print axioms strongHonestBallot_expanded_fresh
#print axioms proofReuse_not_expanded_fresh

end ExplainableCrypto.Helios.Computational
