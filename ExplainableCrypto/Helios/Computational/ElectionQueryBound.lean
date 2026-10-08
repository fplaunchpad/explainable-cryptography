import ExplainableCrypto.Helios.Computational.ElectionExtraction

/-! Derive the real full-election ballot-query budget from its three attacker
callbacks. Key/decryption queries and ordinary randomness are not ballot queries. -/
namespace ExplainableCrypto.Helios.Computational.ElectionQueryBound
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionExtraction
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

def isBallot : (Spec F G).Domain → Prop
  | .inr (.ballot _ _) => True
  | _ => False

instance : DecidablePred (isBallot (F := F) (G := G)) := fun t =>
  match t with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr (.ballot _ _) => inferInstanceAs (Decidable True)
  | .inr (.key _ _ _) => inferInstanceAs (Decidable False)
  | .inr (.decryption _ _ _ _ _) => inferInstanceAs (Decidable False)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem prob_zero {A : Type} (oa : ProbComp A) :
    (liftProb (F := F) (G := G) oa).IsQueryBoundP (isBallot (F := F)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [liftProb]
  | query_bind t next ih =>
    simp only [liftProb,liftComp_bind,liftComp_query] at *
    change (do let a ← liftM ((Spec F G).query (.inl t));
               liftComp (next a) (Spec F G)).IsQueryBoundP (isBallot (F := F)) 0
    simp only [isQueryBoundP_query_bind_iff,isBallot,not_false_eq_true,true_or,Nat.zero_sub,ite_self,true_and]
    intro a
    exact ih a

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem ballot_prob_zero {A : Type} (oa : ProbComp A) :
    (liftComp oa (BallotOracleSpec F G)).IsQueryBoundP (isBallotHashQuery (F := F)) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    rw [liftComp_bind,liftComp_query]
    change (do let a ← liftM ((BallotOracleSpec F G).query (.inl t));
               liftComp (next a) (BallotOracleSpec F G)).IsQueryBoundP (isBallotHashQuery (F := F)) 0
    simp only [isQueryBoundP_query_bind_iff,isBallotHashQuery,not_false_eq_true,true_or,Nat.zero_sub,ite_self,true_and]
    intro a
    exact ih a

omit [DecidableEq F] [AddCommGroup G] [Module F G] in
/-- Lowering retains the ballot-query budget, including all earlier queries.
Auxiliary hash misses remain ordinary randomness in the replay source. -/
theorem lower_bound {A : Type} (oa : Comp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallot (F := F)) n) (cache : Cache F G) :
    ((ElectionReplaySource.lower oa).run cache).IsQueryBoundP (isBallotHashQuery (F := F)) n := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec (HashSpec F G) := IsUniformSpec.ofFintypeInhabited _
  let : IsUniformSpec (BallotHashSpec F G) := IsUniformSpec.ofFintypeInhabited _
  simp only [ElectionReplaySource.lower]
  refine hb.simulateQ_run_of_step ?_ ?_ cache
  · intro t ht state
    cases t with
    | inl _ => simp [isBallot] at ht
    | inr k =>
      cases k with
      | ballot s c =>
        change (do let a ← ballotChallengeOracle s c; pure (a,state)).IsQueryBoundP _ 1
        simp [ballotChallengeOracle,isBallotHashQuery]
      | key _ _ _ => simp [isBallot] at ht
      | decryption _ _ _ _ _ => simp [isBallot] at ht
  · intro t ht state
    cases t with
    | inl n =>
      change (do let a ← liftComp (liftM (unifSpec.query n) : ProbComp _)
                   (BallotOracleSpec F G); pure (a,state)).IsQueryBoundP _ 0
      simpa only [bind_pure_comp,isQueryBoundP_map_iff] using
        ballot_prob_zero (F := F) (G := G) (liftM (unifSpec.query n))
    | inr k =>
      cases k with
      | ballot s c => simp [isBallot] at ht
      | key g pk c =>
        change (ElectionReplaySource.auxiliary (.key g pk c) state).IsQueryBoundP _ 0
        unfold ElectionReplaySource.auxiliary
        split
        · simp
        · simpa only [bind_pure_comp,isQueryBoundP_map_iff] using
            ballot_prob_zero (F := F) (G := G) (uniformSample F)
      | decryption g pk ct share c =>
        change (ElectionReplaySource.auxiliary (.decryption g pk ct share c) state).IsQueryBoundP _ 0
        unfold ElectionReplaySource.auxiliary
        split
        · simp
        · simpa only [bind_pure_comp,isQueryBoundP_map_iff] using
            ballot_prob_zero (F := F) (G := G) (uniformSample F)

omit [DecidableEq F] [AddCommGroup G] [Module F G] in
/-- Lowering retains the ballot-query budget, including all earlier queries.
Auxiliary hash misses remain ordinary randomness in the replay source. -/
theorem source_bound {A : Type} (oa : Comp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallot (F := F)) n) :
    (ElectionReplaySource.source oa).IsQueryBoundP (isBallotHashQuery (F := F)) n := by
  simpa only [ElectionReplaySource.source,isQueryBoundP_map_iff] using
    lower_bound oa n hb (fun _ => none)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem lift_ballot_bound {A : Type} (oa : BallotOracleComp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    (liftBallot oa).IsQueryBoundP (isBallot (F := F)) n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp [liftBallot]
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [liftBallot,simulateQ_bind,simulateQ_spec_query] at *
    cases t with
    | inl k =>
      change (do let a ← liftComp (liftM (unifSpec.query k) : ProbComp _) (Spec F G)
                 simulateQ (ballotImpl F G) (next a)).IsQueryBoundP (isBallot (F := F)) n
      simpa only [Nat.zero_add,liftProb] using isQueryBoundP_bind (prob_zero (F := F) (G := G)
        (liftM (unifSpec.query k))) (fun a _ => by simpa [isBallotHashQuery] using ih a n (hb.2 a))
    | inr key =>
      change (do let a ← ask (.ballot key.1 key.2)
                 simulateQ (ballotImpl F G) (next a)).IsQueryBoundP (isBallot (F := F)) n
      simp only [ask,isQueryBoundP_query_bind_iff,isBallot,isBallotHashQuery] at hb ⊢
      exact ⟨hb.1,fun a => ih a _ (hb.2 a)⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] in
private theorem proof_bound (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) :
    (strongBallotProofWithCoinsOracle stmt wit coins).IsQueryBoundP (isBallotHashQuery (F := F)) 1 := by
  simp [strongBallotProofWithCoinsOracle,ballotChallengeOracle,isBallotHashQuery]

omit [Fintype F] [SampleableType F] in
private theorem verify_bound (g pk : G) (b : Ballot F G 2) :
    (strongBallotVerifyAllOracle g pk b).IsQueryBoundP (isBallotHashQuery (F := F)) 3 := by
  have hv (stmt : BallotStatement G) (p : Proof01 F G) :
      (strongBallotVerifyOracle stmt p).IsQueryBoundP (isBallotHashQuery (F := F)) 1 := by
    simp [strongBallotVerifyOracle,ballotChallengeOracle,isBallotHashQuery]
  unfold strongBallotVerifyAllOracle
  apply isQueryBoundP_bind (n := 1) (m := 2) (hv _ _)
  intro v0 _
  cases v0 <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
  · simp
  · apply isQueryBoundP_bind (n := 1) (m := 1) (hv _ _)
    intro v1 _
    cases v1 <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
    · simp
    · exact hv _ _

omit [Fintype F] [SampleableType F] in
theorem submit_bound (g pk : G) (voter : Fin 3) (board : List (BoardEntry F G))
    (b : Ballot F G 2) :
    (repairedSubmitOracle g pk voter board b).IsQueryBoundP (isBallotHashQuery (F := F)) 3 := by
  unfold repairedSubmitOracle
  apply isQueryBoundP_bind (n := 3) (m := 0) (verify_bound g pk b)
  intro valid _
  cases valid <;> simp only [Bool.false_eq_true,if_false,if_true]
  · simp
  · split <;> simp

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq G] in
private theorem honest_bound (g pk : G) (vote : Bool) (coins : HonestCoins F) :
    (strongHonestBallotWithCoinsOracle g pk vote coins).IsQueryBoundP (isBallotHashQuery (F := F)) 3 := by
  unfold strongHonestBallotWithCoinsOracle
  apply isQueryBoundP_bind (n := 1) (m := 2) (proof_bound _ _ _)
  intro _ _
  apply isQueryBoundP_bind (n := 1) (m := 1) (proof_bound _ _ _)
  intro _ _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using proof_bound (F := F) (G := G) _ _ _

omit [Fintype F] [SampleableType F] in
private theorem pair_bound (g pk : G) (vote : Bool) (alice bob : HonestCoins F) :
    (repairedCastHonestPairWithCoinsOracle g pk vote alice bob).IsQueryBoundP (isBallotHashQuery (F := F)) 12 := by
  unfold repairedCastHonestPairWithCoinsOracle
  apply isQueryBoundP_bind (n := 3) (m := 9) (honest_bound _ _ _ _)
  intro a _
  apply isQueryBoundP_bind (n := 3) (m := 6) (submit_bound _ _ _ _ _)
  intro first _
  apply isQueryBoundP_bind (n := 3) (m := 3) (honest_bound _ _ _ _)
  intro b _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using submit_bound g pk 1 first.2 b

omit [Fintype F] [SampleableType F] in
private theorem prefix_bound (fingerprint : PublicParameters F G → Nat) (g : G)
    (secret nonce : F) (vote : Bool) (alice bob : HonestCoins F) :
    (prefixWithCoins fingerprint g secret nonce vote alice bob).IsQueryBoundP (isBallot (F := F)) 12 := by
  unfold prefixWithCoins
  apply isQueryBoundP_bind (n := 0) (m := 12) (by simp [keyWithCoins,ask,isBallot])
  intro key _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using lift_ballot_bound _ 12 (pair_bound g (secret • g) vote alice bob)

omit [Fintype F] [SampleableType F] in
private theorem finish_bound (secret : F) (nonces : Fin 2 → F) (before : PublicPrefix F G)
    (submission : Ballot F G 2) :
    (finishWithCoins secret nonces before submission).IsQueryBoundP (isBallot (F := F)) 3 := by
  unfold finishWithCoins
  apply isQueryBoundP_bind (n := 3) (m := 0) (lift_ballot_bound _ 3 (submit_bound _ _ _ _ _))
  intro cast _
  simp [partialWithCoins,ask,isBallot]

omit [SampleableType F] in
private theorem sample_bound (fingerprint : PublicParameters F G → Nat) (g : G) (vote : Bool) :
    (samplePrefix fingerprint g vote).IsQueryBoundP (isBallot (F := F)) 12 := by
  unfold samplePrefix
  apply isQueryBoundP_bind (n := 0) (m := 12) (prob_zero _)
  intro secret _
  apply isQueryBoundP_bind (n := 0) (m := 12) (prob_zero _)
  intro nonce _
  apply isQueryBoundP_bind (n := 0) (m := 12) (prob_zero _)
  intro dec _
  apply isQueryBoundP_bind (n := 0) (m := 12) (prob_zero _)
  intro pair _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using prefix_bound fingerprint g secret nonce vote pair.1 pair.2

omit [SampleableType F] in
/-- The protocol contributes at most 15 ballot queries: twelve in honest
construction/validation and three for the adversarial submission. -/
theorem prepared_bound {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP (isBallot (F := F)) nc)
    (hg : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP (isBallot (F := F)) ng) :
    (preparedSource fingerprint g prepare adversary).IsQueryBoundP (isBallot (F := F)) (np+nc+ng+15) := by
  have he : np+nc+ng+15 = np+(0+(12+(nc+(3+ng)))) := by omega
  rw [he,preparedSource]
  apply isQueryBoundP_bind hp
  intro initial _
  apply isQueryBoundP_bind (prob_zero _)
  intro vote _
  simp only [worldSource,bind_assoc,pure_bind]
  apply isQueryBoundP_bind (sample_bound _ _ _)
  intro sample _
  apply isQueryBoundP_bind (hc initial _)
  intro cast _
  apply isQueryBoundP_bind (finish_bound _ _ _ _)
  intro view _
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using hg initial cast.2 view

#print axioms prob_zero
#print axioms ballot_prob_zero
#print axioms lift_ballot_bound
#print axioms submit_bound
#print axioms lower_bound
#print axioms source_bound
#print axioms prepared_bound
end ExplainableCrypto.Helios.Computational.ElectionQueryBound
