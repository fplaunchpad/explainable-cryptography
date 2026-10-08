import ExplainableCrypto.Helios.Computational.HonestBallotOracle

/-! Actual full-proof validation and submission through the shared ballot oracle.
Invalid proofs precede reuse rejection; both rejections retain the board. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def strongBallotVerifyAllOracle (g pk : G) (b : Ballot F G 2) : BallotOracleComp F G Bool := do
  let h0 ← strongBallotVerifyOracle (b.coveredStatement g pk (some 0)) (b.proof 0)
  if !h0 then pure false else do
    let h1 ← strongBallotVerifyOracle (b.coveredStatement g pk (some 1)) (b.proof 1)
    if !h1 then pure false else
      strongBallotVerifyOracle (b.coveredStatement g pk none) b.overall

def repairedSubmitOracle (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    BallotOracleComp F G (Decision × List (BoardEntry F G)) := do
  let valid ← strongBallotVerifyAllOracle g pk b
  if valid then
    if b.ExpandedFreshFor (board.map BoardEntry.ballot) then
      pure (.accepted,board ++ [⟨voter,b⟩])
    else pure (.reusedCiphertext,board)
  else pure (.invalidProof,board)

theorem strongBallotVerifyAllOracle_function (hash : StatementHash F G) (g pk : G)
    (b : Ballot F G 2) :
    simulateQ (ballotFunctionImpl hash) (strongBallotVerifyAllOracle g pk b) =
      pure (decide (b.StrongValid hash g pk)) := by
  by_cases h0 : (b.proof 0).StrongValid hash g pk (b.ciphertext 0) <;>
    by_cases h1 : (b.proof 1).StrongValid hash g pk (b.ciphertext 1) <;>
    by_cases ht : b.overall.StrongValid hash g pk b.aggregate <;>
    simp_all [strongBallotVerifyAllOracle,strongBallotVerifyOracle_function,
      Ballot.coveredStatement,Ballot.coveredCiphertext,Ballot.StrongValid,
      Proof01.StrongValid,Fin.forall_fin_two]

theorem repairedSubmitOracle_function (hash : StatementHash F G) (g pk : G)
    (voter : Fin 3) (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    simulateQ (ballotFunctionImpl hash) (repairedSubmitOracle g pk voter board b) =
      pure (repairedSubmit hash g pk voter board b) := by
  by_cases hv : b.StrongValid hash g pk <;>
    by_cases hf : b.ExpandedFreshFor (board.map BoardEntry.ballot) <;>
    simp [repairedSubmitOracle,strongBallotVerifyAllOracle_function,repairedSubmit,hv,hf]

variable [SampleableType F]

def Ballot.coveredProof {n : Nat} (b : Ballot F G n) : Option (Fin n) → Proof01 F G
  | none => b.overall
  | some i => b.proof i

/-- Each full proof is valid for its actual stored challenge at the full target. -/
def Ballot.CachedStrongValid (g pk : G) (cache : BallotOracleCache F G) (b : Ballot F G 2) : Prop :=
  ∀ i, ∃ c, cache (b.coveredStatement g pk i,(b.coveredProof i).commitment) = some c ∧
    (b.coveredProof i).Valid (fun _ => c) g pk (b.coveredCiphertext i)

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
theorem Ballot.CachedStrongValid.mono (g pk : G) (b : Ballot F G 2)
    {cache next : BallotOracleCache F G} (hv : b.CachedStrongValid g pk cache)
    (hle : cache ≤ next) : b.CachedStrongValid g pk next := by
  intro i
  obtain ⟨c,hc,hv⟩ := hv i
  exact ⟨c,hle hc,hv⟩

theorem strongBallotVerifyAllOracle_cached (g pk : G) (b : Ballot F G 2)
    (cache : BallotOracleCache F G) (hv : b.CachedStrongValid g pk cache) :
    runBallotOracle (strongBallotVerifyAllOracle g pk b) cache = pure (true,cache) := by
  have check (i : Option (Fin 2)) :
      runBallotOracle (strongBallotVerifyOracle (b.coveredStatement g pk i) (b.coveredProof i)) cache =
        pure (true,cache) := by
    obtain ⟨c,hc,hv⟩ := hv i
    rw [runBallotOracle_verify_cached _ _ cache c hc]
    simp [Ballot.coveredStatement,hv]
  have h0 := check (some 0)
  have h1 := check (some 1)
  simp only [Ballot.coveredProof] at h0 h1
  rw [strongBallotVerifyAllOracle,runBallotOracle_bind,h0]
  simp only [pure_bind,Bool.not_true,Bool.false_eq_true,if_false]
  rw [runBallotOracle_bind,h1]
  simp only [pure_bind,Bool.not_true,Bool.false_eq_true,if_false]
  exact check none

/-- Successful complete verification supplies all three full cached proofs;
later component/aggregate queries preserve earlier answers. -/
theorem strongBallotVerifyAllOracle_true_cached (g pk : G) (b : Ballot F G 2)
    (cache : BallotOracleCache F G) (out : Bool × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (strongBallotVerifyAllOracle g pk b) cache))
    (ht : out.1 = true) : b.CachedStrongValid g pk out.2 := by
  rw [strongBallotVerifyAllOracle,runBallotOracle_bind] at ho
  simp only [support_bind,Set.mem_iUnion] at ho
  obtain ⟨v0,h0,ho⟩ := ho
  cases he0 : v0.1 with
  | false =>
    simp [he0,runBallotOracle] at ho
    subst out
    contradiction
  | true =>
    simp only [he0,Bool.not_true,Bool.false_eq_true,if_false] at ho
    rw [runBallotOracle_bind] at ho
    simp only [support_bind,Set.mem_iUnion] at ho
    obtain ⟨v1,h1,ho⟩ := ho
    cases he1 : v1.1 with
    | false =>
      simp [he1,runBallotOracle] at ho
      subst out
      contradiction
    | true =>
      simp only [he1,Bool.not_true,Bool.false_eq_true,if_false] at ho
      obtain ⟨c0,hc0,hp0⟩ := runBallotOracle_verify_true_cached _ _ cache v0 h0 he0
      obtain ⟨c1,hc1,hp1⟩ := runBallotOracle_verify_true_cached _ _ v0.2 v1 h1 he1
      obtain ⟨ct,hct,hpt⟩ := runBallotOracle_verify_true_cached _ _ v1.2 out ho ht
      have h01 := runBallotOracle_cache_le _ v0.2 v1 h1
      have h1t := runBallotOracle_cache_le _ v1.2 out ho
      intro i
      cases i with
      | none => exact ⟨ct,hct,hpt⟩
      | some i =>
        fin_cases i
        · exact ⟨c0,h1t (h01 hc0),hp0⟩
        · exact ⟨c1,h1t hc1,hp1⟩

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
private theorem runBoardOracle_pure {α : Type} (x : α) (cache : BallotOracleCache F G) :
    runBallotOracle (pure x) cache = pure (x,cache) := by
  simp [runBallotOracle]

/-- Actual honest construction leaves all three original full proofs valid
in the final cache, including collisions between their hash targets. -/
theorem strongHonestBallotWithCoinsOracle_cached (g pk : G) (vote : Bool)
    (coins : HonestCoins F) (cache : BallotOracleCache F G)
    (out : Ballot F G 2 × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote coins) cache)) :
    out.1.CachedStrongValid g pk out.2 := by
  simp only [strongHonestBallotWithCoinsOracle,runBallotOracle_bind,runBoardOracle_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  obtain ⟨ca,hca,hpa⟩ := runBallotOracle_honest_cached _ _ _ (by rfl) cache a ha
  obtain ⟨cb,hcb,hpb⟩ := runBallotOracle_honest_cached _ _ _ (by rfl) a.2 b hb
  obtain ⟨cc,hcc,hpc⟩ := runBallotOracle_honest_cached _ _ _ (by rfl) b.2 c hc
  have hab := runBallotOracle_cache_le _ a.2 b hb
  have hbc := runBallotOracle_cache_le _ b.2 c hc
  intro i
  cases i with
  | none =>
    let ballot := assembleHonestBallot g pk vote (coins.nonce 0,coins.nonce 1) a.1 b.1 c.1
    have hct : ballot.aggregate =
        encryptWith g pk (coins.nonce 0+coins.nonce 1) (voteScalar vote) := by
      simp [ballot,assembleHonestBallot,Ballot.aggregate,Fin.sum_univ_two,encryptWith_add]
    have hs : ballot.coveredStatement g pk none =
        honestProofStatement g pk (vote,coins.nonce 0+coins.nonce 1) := by
      simp [Ballot.coveredStatement,Ballot.coveredCiphertext,hct,honestProofStatement]
    change ∃ d, c.2 (ballot.coveredStatement g pk none,c.1.commitment) = some d ∧
      c.1.Valid (fun _ => d) g pk ballot.aggregate
    rw [hs,hct]
    exact ⟨cc,hcc,hpc⟩
  | some i =>
    fin_cases i
    · exact ⟨ca,hbc (hab hca),hpa⟩
    · exact ⟨cb,hbc hcb,hpb⟩

/-- Historical nonzero sampling and real requests derive cached validity;
no caller proof-validity premise is needed for the returned honest ballot. -/
theorem strongHonestBallotOracle_real_cached [Fintype F] (g pk : G) (vote : Bool)
    (state : BallotProofOracleState F G)
    (out : Ballot F G 2 × BallotProofOracleState F G)
    (ho : out ∈ support (runBallotProofReal g pk (strongHonestBallotOracle g pk vote) state)) :
    out.1.CachedStrongValid g pk out.2.1 := by
  have he := strongHonestBallotOracle_real_eq g pk vote state.1 state.2
  have hs := (mem_support_iff_of_evalSPMF_eq he out).mp ho
  simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hs
  obtain ⟨coins,hcoins,ballot,hballot,rfl⟩ := hs
  exact strongHonestBallotWithCoinsOracle_cached g pk vote coins state.1 ballot hballot

/-- Actual accepting oracle executions append the supplied ballot and pass
expanded component/aggregate weeding. No static-hash freshness premise. -/
theorem repairedSubmitOracle_accepted (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) (cache : BallotOracleCache F G)
    (out : (Decision × List (BoardEntry F G)) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (repairedSubmitOracle g pk voter board b) cache))
    (ha : out.1.1 = .accepted) :
    b.CachedStrongValid g pk out.2 ∧ b.ExpandedFreshFor (board.map BoardEntry.ballot) ∧
      out.1.2 = board ++ [⟨voter,b⟩] := by
  rw [repairedSubmitOracle,runBallotOracle_bind] at ho
  simp only [support_bind,Set.mem_iUnion] at ho
  obtain ⟨v,hv,ho⟩ := ho
  cases he : v.1 <;> simp only [he,Bool.false_eq_true,if_false,if_true] at ho
  · simp [runBallotOracle] at ho
    subst out
    contradiction
  · split at ho
    · simp [runBallotOracle] at ho
      subst out
      exact ⟨strongBallotVerifyAllOracle_true_cached g pk b cache v hv he,by assumption,rfl⟩
    · simp [runBallotOracle] at ho
      subst out
      contradiction

theorem repairedSubmitOracle_rejected_preserves_board (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) (cache : BallotOracleCache F G)
    (out : (Decision × List (BoardEntry F G)) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (repairedSubmitOracle g pk voter board b) cache))
    (ha : out.1.1 ≠ .accepted) : out.1.2 = board := by
  rw [repairedSubmitOracle,runBallotOracle_bind] at ho
  simp only [support_bind,Set.mem_iUnion] at ho
  obtain ⟨v,hv,ho⟩ := ho
  cases he : v.1 <;> simp only [he,Bool.false_eq_true,if_false,if_true] at ho
  · simp [runBallotOracle] at ho
    subst out
    rfl
  · split at ho
    · simp [runBallotOracle] at ho
      subst out
      contradiction
    · simp [runBallotOracle] at ho
      subst out
      rfl

/-- Weeding in actual accepted oracle runs excludes all earlier covered targets. -/
theorem repairedSubmitOracle_accepted_target_ne (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b old : Ballot F G 2) (cache : BallotOracleCache F G)
    (out : (Decision × List (BoardEntry F G)) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (repairedSubmitOracle g pk voter board b) cache))
    (ha : out.1.1 = .accepted) (hmem : old ∈ board.map BoardEntry.ballot)
    (i j : Option (Fin 2)) : b.coveredStatement g pk i ≠ old.coveredStatement g pk j := by
  intro he
  exact (repairedSubmitOracle_accepted g pk voter board b cache out ho ha).2.1 old hmem i j
    (congrArg BallotStatement.ciphertext he)

/-- Two actual oracle submissions with the original explicit honest coins. -/
def repairedCastHonestPairWithCoinsOracle (g pk : G) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) :
    BallotOracleComp F G ((Decision × Decision) × List (BoardEntry F G)) := do
  let alice ← strongHonestBallotWithCoinsOracle g pk vote aliceCoins
  let first ← repairedSubmitOracle g pk 0 [] alice
  let bob ← strongHonestBallotWithCoinsOracle g pk (!vote) bobCoins
  let second ← repairedSubmitOracle g pk 1 first.2 bob
  pure ((first.1,second.1),second.2)

/-- Sampled honest voters and their actual verification/board decisions in the
same interface used by adaptive honest-proof simulation. -/
noncomputable def repairedCastHonestPairOracle [Fintype F] (g pk : G) (vote : Bool) :
    OracleComp (BallotProofOracleSpec F G) ((Decision × Decision) × List (BoardEntry F G)) := do
  let alice ← strongHonestBallotOracle g pk vote
  let first ← liftComp (repairedSubmitOracle g pk 0 [] alice) _
  let bob ← strongHonestBallotOracle g pk (!vote)
  let second ← liftComp (repairedSubmitOracle g pk 1 first.2 bob) _
  pure ((first.1,second.1),second.2)

omit [SampleableType F] in
theorem repairedCastHonestPairWithCoinsOracle_function (hash : StatementHash F G) (g pk : G)
    (vote : Bool) (aliceCoins bobCoins : HonestCoins F) :
    simulateQ (ballotFunctionImpl hash)
      (repairedCastHonestPairWithCoinsOracle g pk vote aliceCoins bobCoins) =
      pure (repairedCastHonestPair hash g pk vote aliceCoins bobCoins) := by
  simp [repairedCastHonestPairWithCoinsOracle,strongHonestBallotWithCoinsOracle_function,
    repairedSubmitOracle_function,repairedCastHonestPair]

#print axioms strongBallotVerifyAllOracle_function
#print axioms repairedSubmitOracle_function
#print axioms Ballot.CachedStrongValid.mono
#print axioms strongBallotVerifyAllOracle_cached
#print axioms strongBallotVerifyAllOracle_true_cached
#print axioms strongHonestBallotWithCoinsOracle_cached
#print axioms strongHonestBallotOracle_real_cached
#print axioms repairedSubmitOracle_accepted
#print axioms repairedSubmitOracle_rejected_preserves_board
#print axioms repairedSubmitOracle_accepted_target_ne
#print axioms repairedCastHonestPairWithCoinsOracle_function
end ExplainableCrypto.Helios.Computational
