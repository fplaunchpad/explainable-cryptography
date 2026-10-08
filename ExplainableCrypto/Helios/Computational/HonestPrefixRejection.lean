import ExplainableCrypto.Helios.Computational.HonestPrefixOracle

/-! Rejection of the actual sampled oracle prefix is charged to historical
nonce collisions. No caller validity or accepted-prefix premise is used. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
private theorem runPrefixOracle_pure {α : Type} (x : α) (cache : BallotOracleCache F G) :
    runBallotOracle (pure x) cache = pure (x,cache) := by simp [runBallotOracle]

omit [DecidableEq F] in
/-- The actual returned ciphertexts have the original covered nonce coordinates,
including the aggregate sum. Hash responses and proof coins cannot change them. -/
theorem strongHonestBallotWithCoinsOracle_covered_fst (g pk : G) (vote : Bool)
    (coins : HonestCoins F) (cache : BallotOracleCache F G)
    (out : Ballot F G 2 × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote coins) cache)) :
    ∀ i, (out.1.coveredCiphertext i).1 = coins.coveredNonce i • g := by
  simp only [strongHonestBallotWithCoinsOracle,runBallotOracle_bind,runPrefixOracle_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  intro i
  cases i with
  | none => simp [Ballot.coveredCiphertext,Ballot.aggregate,assembleHonestBallot,
      HonestCoins.coveredNonce,Fin.sum_univ_two,encryptWith,add_smul]
  | some i => fin_cases i <;> rfl

private theorem submit_cached (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) (cache : BallotOracleCache F G)
    (hv : b.CachedStrongValid g pk cache)
    (hf : b.ExpandedFreshFor (board.map BoardEntry.ballot)) :
    runBallotOracle (repairedSubmitOracle g pk voter board b) cache =
      pure ((.accepted,board ++ [⟨voter,b⟩]),cache) := by
  rw [repairedSubmitOracle,runBallotOracle_bind,strongBallotVerifyAllOracle_cached g pk b cache hv]
  simp [hf,runBallotOracle]

/-- Collision-free historical coins force acceptance in every supported actual
oracle run, for arbitrary initial cache. Honest full validity is derived. -/
theorem repairedCastHonestPairWithCoinsOracle_accepts_of_collisionFree (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (aliceCoins bobCoins : HonestCoins F) (hfree : ExpandedCollisionFree aliceCoins bobCoins)
    (cache : BallotOracleCache F G)
    (out : ((Decision × Decision) × List (BoardEntry F G)) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle
      (repairedCastHonestPairWithCoinsOracle g pk vote aliceCoins bobCoins) cache)) :
    out.1.1 = (.accepted,.accepted) := by
  simp only [repairedCastHonestPairWithCoinsOracle,runBallotOracle_bind,runPrefixOracle_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨alice,halice,first,hfirst,bob,hbob,second,hsecond,rfl⟩ := ho
  have hav := strongHonestBallotWithCoinsOracle_cached g pk vote aliceCoins cache alice halice
  rw [submit_cached g pk 0 [] alice.1 alice.2 hav (by simp [Ballot.ExpandedFreshFor])] at hfirst
  simp only [support_pure,Set.mem_singleton_iff,List.nil_append] at hfirst
  subst first
  have hbv := strongHonestBallotWithCoinsOracle_cached g pk (!vote) bobCoins alice.2 bob hbob
  have haf := strongHonestBallotWithCoinsOracle_covered_fst g pk vote aliceCoins cache alice halice
  have hbf := strongHonestBallotWithCoinsOracle_covered_fst g pk (!vote) bobCoins alice.2 bob hbob
  have hf : bob.1.ExpandedFreshFor ([⟨0,alice.1⟩].map BoardEntry.ballot) := by
    intro old hold i j he
    simp only [List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hold
    subst old
    have hx := congrArg Prod.fst he
    rw [hbf,haf] at hx
    exact hfree i j (hg hx)
  rw [submit_cached g pk 1 [⟨0,alice.1⟩] bob.1 bob.2 hbv hf] at hsecond
  simp only [support_pure,Set.mem_singleton_iff] at hsecond
  subst second
  rfl

/-- Actual real prefix rejection is bounded by the existing historical nonce
collision event, with both decisions and all cache/flag outcomes retained. -/
theorem repairedCastHonestPairOracle_real_rejection_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (state : BallotProofOracleState F G) :
    Pr[fun out => out.1.1 ≠ (.accepted,.accepted) |
      runBallotProofReal g pk (repairedCastHonestPairOracle g pk vote) state] ≤
      9 * noncePointBound F := by
  classical
  have he := repairedCastHonestPairOracle_real_eq g pk vote state
  rw [probEvent_congr' (fun _ _ => Iff.rfl) he]
  apply le_trans ?_ (drawHonestPair_expanded_collision_le (F := F))
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro pair
  by_cases hf : ExpandedCollisionFree pair.1 pair.2
  · simp only [hf,not_true_eq_false,ite_false]
    have hz : Pr[fun out => out.1.1 ≠ (.accepted,.accepted) |
        runBallotOracle (repairedCastHonestPairWithCoinsOracle g pk vote pair.1 pair.2) state.1] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro out ho hn
      exact hn (repairedCastHonestPairWithCoinsOracle_accepts_of_collisionFree
        g pk hg vote pair.1 pair.2 hf state.1 out ho)
    simp only [bind_pure_comp,probEvent_map,Function.comp_def,hz,mul_zero,le_refl]
  · simp only [hf,not_false_eq_true,ite_true]
    exact mul_le_of_le_one_right' probEvent_le_one

omit [SampleableType F] in
private theorem verifyAll_query_bound (g pk : G) (b : Ballot F G 2) :
    (liftComp (strongBallotVerifyAllOracle g pk b) (BallotProofOracleSpec F G)).IsQueryBoundP
      growsBallotCache 3 := by
  have hv (stmt : BallotStatement G) (p : Proof01 F G) :
      (liftComp (strongBallotVerifyOracle stmt p) (BallotProofOracleSpec F G)).IsQueryBoundP
        growsBallotCache 1 := by
    simp only [strongBallotVerifyOracle,ballotChallengeOracle,bind_pure_comp]
    change (liftM ((BallotProofOracleSpec F G).query (.inl (.inr (stmt,p.commitment)))) :
      OracleComp (BallotProofOracleSpec F G) F).IsQueryBoundP growsBallotCache 1
    simp [growsBallotCache]
  rw [strongBallotVerifyAllOracle,liftComp_bind]
  apply isQueryBoundP_bind (n := 1) (m := 2) (hv _ _)
  intro h0 _
  cases h0 <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
  · simp
  · rw [liftComp_bind]
    apply isQueryBoundP_bind (n := 1) (m := 1) (hv _ _)
    intro h1 _
    cases h1 <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,if_false,if_true]
    · simp
    · exact hv _ _

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [SampleableType F] in
private theorem raw_no_proof_requests {α : Type} (oa : BallotOracleComp F G α) :
    (liftComp oa (BallotProofOracleSpec F G)).IsQueryBoundP isBallotProofRequest 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    rw [liftComp_bind]
    cases t with
    | inl n =>
      change (do let u ← liftM ((BallotProofOracleSpec F G).query (.inl (.inl n)))
                 liftComp (next u) (BallotProofOracleSpec F G)).IsQueryBoundP isBallotProofRequest 0
      simp [isBallotProofRequest,ih]
    | inr key =>
      change (do let u ← liftM ((BallotProofOracleSpec F G).query (.inl (.inr key)))
                 liftComp (next u) (BallotProofOracleSpec F G)).IsQueryBoundP isBallotProofRequest 0
      simp [isBallotProofRequest,ih]

omit [SampleableType F] in
/-- Short-circuit full verification uses at most three hash requests and never
makes an honest proof request, for every supplied ballot and board. -/
theorem repairedSubmitOracle_query_bounds (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G)).IsQueryBoundP
      growsBallotCache 3 ∧
    (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G)).IsQueryBoundP
      isBallotProofRequest 0 := by
  refine ⟨?_,raw_no_proof_requests _⟩
  rw [repairedSubmitOracle,liftComp_bind]
  apply isQueryBoundP_bind (n := 3) (m := 0) (verifyAll_query_bound g pk b)
  intro valid _
  cases valid <;> simp only [Bool.false_eq_true,if_false,if_true]
  · simp
  · split <;> simp

omit [SampleableType F] in
/-- The actual sampled honest prefix has six proof requests and at most six
verification hashes. Nonce draws contribute no hash/proof requests. -/
theorem repairedCastHonestPairOracle_query_bounds [Fintype F] (g pk : G) (vote : Bool) :
    (repairedCastHonestPairOracle (F := F) g pk vote).IsQueryBoundP growsBallotCache 12 ∧
    (repairedCastHonestPairOracle (F := F) g pk vote).IsQueryBoundP isBallotProofRequest 6 := by
  unfold repairedCastHonestPairOracle
  constructor
  · apply isQueryBoundP_bind (n := 3) (m := 9) (strongHonestBallotOracle_query_bounds g pk vote).1
    intro alice _
    apply isQueryBoundP_bind (n := 3) (m := 6) (repairedSubmitOracle_query_bounds g pk 0 [] alice).1
    intro first _
    apply isQueryBoundP_bind (n := 3) (m := 3) (strongHonestBallotOracle_query_bounds g pk (!vote)).1
    intro bob _
    apply isQueryBoundP_bind (n := 3) (m := 0) (repairedSubmitOracle_query_bounds g pk 1 first.2 bob).1
    simp
  · apply isQueryBoundP_bind (n := 3) (m := 3) (strongHonestBallotOracle_query_bounds g pk vote).2
    intro alice _
    apply isQueryBoundP_bind (n := 0) (m := 3) (repairedSubmitOracle_query_bounds g pk 0 [] alice).2
    intro first _
    apply isQueryBoundP_bind (n := 3) (m := 0) (strongHonestBallotOracle_query_bounds g pk (!vote)).2
    intro bob _
    apply isQueryBoundP_bind (n := 0) (m := 0) (repairedSubmitOracle_query_bounds g pk 1 first.2 bob).2
    simp

/-- State-inclusive adaptive distance for the actual prefix, with its request
budgets derived above rather than supplied by the caller. -/
theorem repairedCastHonestPairOracle_simulation_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (state : BallotProofOracleState F G) (k : Nat) (hk : BallotCacheBound state.1 k) :
    tvDist (runBallotProofReal g pk (repairedCastHonestPairOracle g pk vote) state)
      (runBallotProofSim g pk (repairedCastHonestPairOracle g pk vote) state) ≤
        6 * (15 + (k : ℝ)) / (Fintype.card F : ℝ) := by
  have hb := repairedCastHonestPairOracle_query_bounds (F := F) g pk vote
  have h := strongBallot_programming_distance_le g pk hg (repairedCastHonestPairOracle g pk vote)
    12 6 k hb.1 hb.2 state hk
  convert h using 1
  push_cast
  ring

/-- Actual simulated rejection includes the real nonce-collision loss and the
state-inclusive simulation distance. No bad cache or rejection is discarded. -/
theorem repairedCastHonestPairOracle_sim_rejection_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (state : BallotProofOracleState F G) (k : Nat) (hk : BallotCacheBound state.1 k) :
    Pr[fun out => out.1.1 ≠ (.accepted,.accepted) |
      runBallotProofSim g pk (repairedCastHonestPairOracle g pk vote) state] ≤
      9 * noncePointBound F + ENNReal.ofReal (6 * (15 + (k : ℝ)) / (Fintype.card F : ℝ)) := by
  classical
  let realRun := runBallotProofReal g pk (repairedCastHonestPairOracle g pk vote) state
  let simRun := runBallotProofSim g pk (repairedCastHonestPairOracle g pk vote) state
  let rejected : ((Decision × Decision) × List (BoardEntry F G)) × BallotProofOracleState F G → Bool :=
    fun out => decide (out.1.1 ≠ (.accepted,.accepted))
  have hd := (abs_probOutput_toReal_sub_le_tvDist (rejected <$> realRun) (rejected <$> simRun)).trans
    ((tvDist_map_le rejected realRun simRun).trans
      (repairedCastHonestPairOracle_simulation_le g pk hg vote state k hk))
  simp only [probOutput_map,rejected,decide_eq_true_eq] at hd
  have hb := repairedCastHonestPairOracle_real_rejection_le g pk hg vote state
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hfinite : 9 * noncePointBound F ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.inv_ne_top.mpr
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hq))
  have hr := ENNReal.toReal_mono hfinite hb
  have hnonneg : 0 ≤ 6 * (15 + (k : ℝ)) / (Fintype.card F : ℝ) := by positivity
  apply (ENNReal.toReal_le_toReal probEvent_ne_top (ENNReal.add_ne_top.mpr
    ⟨hfinite,ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hnonneg]
  dsimp only [realRun,simRun] at hd
  linarith [(abs_le.mp hd).1]

/-- Empty-initialized replayable programmed execution inherits the same honest
rejection bound through its proved runtime correspondence. -/
theorem repairedCastHonestPairOracle_programmed_rejection_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool) :
    Pr[fun out => out.1.1.1 ≠ (.accepted,.accepted) |
      runBallotProgrammed g pk (repairedCastHonestPairOracle (F := F) g pk vote)] ≤
      9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)) := by
  have h := repairedCastHonestPairOracle_sim_rejection_le g pk hg vote (∅,false) 0 BallotCacheBound.empty
  rw [← ballotProgrammed_runtime_eq,probEvent_map] at h
  simpa only [Function.comp_def,Nat.cast_zero,add_zero,mul_one,show (6 : ℝ) * 15 = 90 by norm_num] using h

#print axioms strongHonestBallotWithCoinsOracle_covered_fst
#print axioms repairedCastHonestPairWithCoinsOracle_accepts_of_collisionFree
#print axioms repairedCastHonestPairOracle_real_rejection_le
#print axioms repairedSubmitOracle_query_bounds
#print axioms repairedCastHonestPairOracle_query_bounds
#print axioms repairedCastHonestPairOracle_simulation_le
#print axioms repairedCastHonestPairOracle_sim_rejection_le
#print axioms repairedCastHonestPairOracle_programmed_rejection_le
end ExplainableCrypto.Helios.Computational
