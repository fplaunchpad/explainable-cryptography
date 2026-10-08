import ExplainableCrypto.Helios.Computational.HonestPrefixRejection

/-! An adaptive raw attacker receives actual honest decisions and the retained
board. The original submission executes through the same programmed oracle. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

abbrev HonestPrefixView (F G : Type) := (Decision × Decision) × List (BoardEntry F G)

structure RepairedSubmissionResult (F G : Type) where
  honest : HonestPrefixView F G
  ballot : Ballot F G 2
  decision : Decision
  board : List (BoardEntry F G)

/-- This is the ballot-submission phase, not the full election game. Public key
and generator can be supplied to the attacker by its enclosing game. -/
noncomputable def repairedSubmissionOracle [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    OracleComp (BallotProofOracleSpec F G) (RepairedSubmissionResult F G) := do
  let honest ← repairedCastHonestPairOracle g pk vote
  let ballot ← liftComp (attacker honest) _
  let cast ← liftComp (repairedSubmitOracle g pk 2 honest.2 ballot) _
  pure ⟨honest,ballot,cast.1,cast.2⟩

omit [DecidableEq F] in
private theorem runSim_bind {α β : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (next : α → OracleComp (BallotProofOracleSpec F G) β) (state : BallotProofOracleState F G) :
    runBallotProofSim g pk (oa >>= next) state = (do
      let out ← runBallotProofSim g pk oa state
      runBallotProofSim g pk (next out.1) out.2) := by
  simp only [runBallotProofSim,simulateQ_bind,StateT.run_bind]

omit [DecidableEq F] in
/-- Raw queries in the simulated source use the original lazy oracle and preserve
the sticky flag. Honest proof requests are absent from this raw computation. -/
theorem runBallotProofSim_raw {α : Type} (g pk : G) (oa : BallotOracleComp F G α)
    (state : BallotProofOracleState F G) :
    runBallotProofSim g pk (liftComp oa (BallotProofOracleSpec F G)) state =
      (fun out => (out.1,(out.2,state.2))) <$> runBallotOracle oa state.1 := by
  induction oa using OracleComp.inductionOn generalizing state with
  | pure x => simp [runBallotProofSim,runBallotOracle]
  | query_bind t next ih =>
    rw [liftComp_bind,runSim_bind,runBallotOracle_bind]
    have hq : runBallotProofSim g pk
        (liftComp (liftM ((BallotOracleSpec F G).query t) : BallotOracleComp F G _)
          (BallotProofOracleSpec F G)) state =
        (fun out => (out.1,(out.2,state.2))) <$>
          runBallotOracle (liftM ((BallotOracleSpec F G).query t)) state.1 := by
      cases t with
      | inl n =>
        change runBallotProofSim g pk
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inl n)))) state = _
        simp [runBallotProofSim,ballotProofSimImpl,ballotProofImpl,
          QueryImpl.add,runBallotOracle,StateT.run]
      | inr key =>
        change runBallotProofSim g pk
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inr key)))) state = _
        simp [runBallotProofSim,ballotProofSimImpl,ballotProofImpl,
          QueryImpl.add,runBallotOracle,StateT.run]
    rw [hq]
    simp only [bind_map_left,map_bind]
    exact bind_congr (fun out => ih out.1 (out.2,state.2))

/-- Actual programmed submission derives full validity in the final shadow cache.
The initial invariant will be supplied by the actual prefix/attacker execution. -/
theorem repairedSubmitProgrammed_accepted_cached (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv state live)
    (out : ((Decision × List (BoardEntry F G)) × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G))).run state) live))
    (ha : out.1.1.1 = .accepted) : b.CachedStrongValid g pk out.1.2.cache := by
  have hm : (out.1.1,out.1.2.toSimState) ∈ support
      ((fun z => (z.1.1,z.1.2.toSimState)) <$>
        runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
          (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G))).run state) live) :=
    by rw [support_map]; exact ⟨out,ho,rfl⟩
  rw [ballotProgrammed_runtime_eq_of_inv g pk _ state live hi,runBallotProofSim_raw,support_map] at hm
  obtain ⟨raw,hraw,he⟩ := hm
  have hv := (repairedSubmitOracle_accepted g pk voter board b state.cache raw hraw
    ((congrArg (fun x => x.1.1) he).trans ha)).1
  have hc : raw.2 = out.1.2.cache := congrArg (fun x => x.2.1) he
  rwa [hc] at hv

/-- In the composed actual execution, accepted malicious full proofs verify in
the live cache when both honest decisions accepted. All cache consistency,
recorded-target exclusion and full validity are derived from that execution. -/
theorem repairedSubmissionOracle_accepted_live [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2))
    (out : (RepairedSubmissionResult F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)))
    (hhonest : out.1.1.honest.1 = (.accepted,.accepted))
    (haccept : out.1.1.decision = .accepted) :
    ∀ i, runBallotOracle
      (strongBallotVerifyOracle (out.1.1.ballot.coveredStatement g pk i) (out.1.1.ballot.coveredProof i))
      out.2 = pure (true,out.2) := by
  have hfinal := ballotProgrammed_request_provenance g pk _ out ho
  simp only [runBallotProgrammed,repairedSubmissionOracle,runProgrammed_bind,
    runProgrammed_pure,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨honest,hprefix,made,hmade,cast,hcast,rfl⟩ := ho
  have hmadeRun : made ∈ support (runBallotProgrammed g pk (do
      let view ← repairedCastHonestPairOracle g pk vote
      liftComp (attacker view) (BallotProofOracleSpec F G))) := by
    simp only [runBallotProgrammed,runProgrammed_bind,support_bind,Set.mem_iUnion]
    exact ⟨honest,hprefix,hmade⟩
  have hi := ballotProgrammed_request_provenance g pk _ made hmadeRun
  have hv := repairedSubmitProgrammed_accepted_cached g pk 2 honest.1.1.2 made.1.1 _ _ hi cast hcast haccept
  have hn := repairedHonestPrefix_accepted_target_exclusion g pk vote honest hprefix hhonest
    (attacker honest.1.1) made hmade cast hcast haccept
  intro i
  obtain ⟨c,hc,hvalid⟩ := hv i
  have hcache : cast.2 (made.1.1.coveredStatement g pk i,(made.1.1.coveredProof i).commitment) = some c :=
    (hfinal.2 _ (hn i)).symm.trans hc
  rw [runBallotOracle_verify_cached _ _ _ c hcache]
  simp [Ballot.coveredStatement,hvalid]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] [SampleableType F] in
theorem raw_lift_hash_bound {α : Type} (oa : BallotOracleComp F G α) (n : Nat)
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    (liftComp oa (BallotProofOracleSpec F G)).IsQueryBoundP growsBallotCache n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure x => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    rw [liftComp_bind]
    cases t with
    | inl k =>
      change (do let u ← liftM ((BallotProofOracleSpec F G).query (.inl (.inl k)))
                 liftComp (next u) (BallotProofOracleSpec F G)).IsQueryBoundP growsBallotCache n
      simp only [isQueryBoundP_query_bind_iff,growsBallotCache,not_false_eq_true,true_or,true_and]
      intro u
      exact ih u n (by simpa [isBallotHashQuery] using hb.2 u)
    | inr key =>
      change (do let u ← liftM ((BallotProofOracleSpec F G).query (.inl (.inr key)))
                 liftComp (next u) (BallotProofOracleSpec F G)).IsQueryBoundP growsBallotCache n
      simp only [isQueryBoundP_query_bind_iff,growsBallotCache,not_true_eq_false,false_or]
      exact ⟨by simpa [isBallotHashQuery] using hb.1,
        fun u => ih u (n-1) (by simpa [isBallotHashQuery] using hb.2 u)⟩

omit [SampleableType F] in
/-- The entire prefix, adaptive attacker and original submission has the derived
hash/proof budget n+15, given the attacker's raw hash budget n. -/
theorem repairedSubmissionOracle_query_bound [Fintype F] (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n : Nat)
    (hb : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := F)) n) :
    (repairedSubmissionOracle g pk vote attacker).IsQueryBoundP growsBallotCache (n+15) := by
  unfold repairedSubmissionOracle
  rw [show n+15 = 12+(n+3) by omega]
  apply isQueryBoundP_bind (n := 12) (m := n+3) (repairedCastHonestPairOracle_query_bounds (F := F) g pk vote).1
  intro view _
  apply isQueryBoundP_bind (n := n) (m := 3) (raw_lift_hash_bound (attacker view) n (hb view))
  intro ballot _
  apply isQueryBoundP_bind (n := 3) (m := 0) (repairedSubmitOracle_query_bounds g pk 2 view.2 ballot).1
  simp

/-- Continuing with the actual attacker and submission cannot increase the
probability of the already determined honest-prefix rejection event. -/
theorem repairedSubmissionOracle_prefix_rejection_le [Fintype F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) :
    Pr[fun out => out.1.1.honest.1 ≠ (.accepted,.accepted) |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)] ≤
      9 * noncePointBound F + ENNReal.ofReal (90 / (Fintype.card F : ℝ)) := by
  classical
  apply le_trans ?_ (repairedCastHonestPairOracle_programmed_rejection_le g pk hg vote)
  rw [runBallotProgrammed,repairedSubmissionOracle,runProgrammed_bind,probEvent_bind_eq_tsum,
    probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro honest
  by_cases hh : honest.1.1.1 = (.accepted,.accepted)
  · rw [if_neg (not_not_intro hh)]
    have hz : Pr[fun out => out.1.1.honest.1 ≠ (.accepted,.accepted) |
        runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) (do
          let ballot ← liftComp (attacker honest.1.1) (BallotProofOracleSpec F G)
          let cast ← liftComp (repairedSubmitOracle g pk 2 honest.1.1.2 ballot) (BallotProofOracleSpec F G)
          pure (⟨honest.1.1,ballot,cast.1,cast.2⟩ : RepairedSubmissionResult F G))).run honest.1.2) honest.2] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro out ho hn
      simp only [runProgrammed_bind,runProgrammed_pure,support_bind,support_pure,
        Set.mem_iUnion,Set.mem_singleton_iff] at ho
      obtain ⟨made,hmade,cast,hcast,rfl⟩ := ho
      exact hn hh
    rw [hz,mul_zero]
  · rw [if_pos hh]
    exact mul_le_of_le_one_right' probEvent_le_one

#print axioms raw_lift_hash_bound
#print axioms runBallotProofSim_raw
#print axioms repairedSubmitProgrammed_accepted_cached
#print axioms repairedSubmissionOracle_accepted_live
#print axioms repairedSubmissionOracle_query_bound
#print axioms repairedSubmissionOracle_prefix_rejection_le
end ExplainableCrypto.Helios.Computational
