import ExplainableCrypto.Helios.Computational.RepairedBoardOracle

/-! Compose the two historical honest samplers with actual oracle submissions.
Public decisions and retained boards are part of the returned prefix. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [Fintype F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

omit [DecidableEq F] in
private theorem runHonestReal_bind {α β : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (next : α → OracleComp (BallotProofOracleSpec F G) β) (state : BallotProofOracleState F G) :
    runBallotProofReal g pk (oa >>= next) state = (do
      let out ← runBallotProofReal g pk oa state
      runBallotProofReal g pk (next out.1) out.2) := by
  simp only [runBallotProofReal,simulateQ_bind,StateT.run_bind]

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
private theorem realRequest_lower_raw {α : Type} (g pk : G) (oa : BallotOracleComp F G α) :
    simulateQ (ballotRealRequestImpl g pk) (liftComp oa (BallotProofOracleSpec F G)) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    rw [liftComp_bind,simulateQ_bind]
    have hq : simulateQ (ballotRealRequestImpl (F := F) g pk)
        (liftComp (liftM ((BallotOracleSpec F G).query t) : BallotOracleComp F G _) (BallotProofOracleSpec F G)) =
        liftM ((BallotOracleSpec F G).query t) := by
      cases t with
      | inl n =>
        change simulateQ (ballotRealRequestImpl (F := F) g pk)
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inl n)))) = _
        rw [simulateQ_spec_query]
        rfl
      | inr key =>
        change simulateQ (ballotRealRequestImpl (F := F) g pk)
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inr key)))) = _
        rw [simulateQ_spec_query]
        rfl
    rw [hq]
    exact bind_congr ih

omit [DecidableEq F] in
private theorem runHonestReal_raw {α : Type} (g pk : G) (oa : BallotOracleComp F G α)
    (state : BallotProofOracleState F G) :
    runBallotProofReal g pk (liftComp oa (BallotProofOracleSpec F G)) state =
      (fun out => (out.1,(out.2,state.2))) <$> runBallotOracle oa state.1 := by
  rw [ballotRealRequest_runtime_eq,realRequest_lower_raw]

omit [DecidableEq F] in
private theorem runHonestReal_pure {α : Type} (g pk : G) (x : α) (state : BallotProofOracleState F G) :
    runBallotProofReal g pk (pure x) state = pure (x,state) := by
  simp [runBallotProofReal]

omit [DecidableEq F] in
private theorem runHonestReal_ballot_bind {α : Type} (g pk : G) (vote : Bool)
    (next : Ballot F G 2 → OracleComp (BallotProofOracleSpec F G) α)
    (state : BallotProofOracleState F G) :
    𝒮[runBallotProofReal g pk (strongHonestBallotOracle g pk vote >>= next) state] =
      𝒮[do let coins ← drawHonestCoins F
           let out ← runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote coins) state.1
           runBallotProofReal g pk (next out.1) (out.2,state.2)] := by
  rw [runHonestReal_bind,evalSPMF_bind,strongHonestBallotOracle_real_eq,← evalSPMF_bind]
  simp only [bind_assoc,pure_bind]

/-- The whole sampled honest prefix agrees with the historical honest-pair coin
sampler and explicit-coin oracle execution, including decisions, board, cache and flag. -/
theorem repairedCastHonestPairOracle_real_eq (g pk : G) (vote : Bool)
    (state : BallotProofOracleState F G) :
    𝒮[runBallotProofReal g pk (repairedCastHonestPairOracle g pk vote) state] =
      𝒮[do let coins ← drawHonestPair F
           let out ← runBallotOracle
             (repairedCastHonestPairWithCoinsOracle g pk vote coins.1 coins.2) state.1
           pure (out.1,(out.2,state.2))] := by
  rw [repairedCastHonestPairOracle,runHonestReal_ballot_bind]
  simp only [runHonestReal_bind,runHonestReal_raw,bind_map_left]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext aliceCoins
    rw [evalSPMF_bind]; arg 2; ext alice
    rw [evalSPMF_bind]; arg 2; ext first
    rw [evalSPMF_bind]; arg 1
    rw [strongHonestBallotOracle_real_eq]
  simp only [← evalSPMF_bind,runHonestReal_pure,bind_assoc,pure_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext aliceCoins
    rw [evalSPMF_bind]; arg 2; ext alice
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext aliceCoins
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  simp only [drawHonestPair,bind_assoc,pure_bind,repairedCastHonestPairWithCoinsOracle,
    runBallotOracle_bind]
  simp [runBallotOracle]

omit [Fintype F] [DecidableEq F] in
theorem runProgrammed_bind {α β : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (next : α → OracleComp (BallotProofOracleSpec F G) β)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) (oa >>= next)).run state) live =
      (do let out ← runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run state) live
          runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) (next out.1.1)).run out.1.2) out.2) := by
  simp only [simulateQ_bind,StateT.run_bind,runBallotOracle_bind]

omit [Fintype F] [DecidableEq F] in
theorem runProgrammed_pure {α : Type} (g pk : G) (x : α)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) (pure x)).run state) live =
      pure ((x,state),live) := by
  simp [runBallotOracle]

omit [Fintype F] [DecidableEq F] [Field F] [AddCommGroup G] [Module F G] in
private theorem programmed_raw_step_list (t : (BallotOracleSpec F G).Domain)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : ((BallotOracleSpec F G).Range t × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballotProgrammedRaw (F := F) (G := G) t).run state) live)) :
    out.1.2.programmed = state.programmed := by
  cases t with
  | inl n =>
    change out ∈ support (runBallotOracle (do
      let u ← liftComp (liftM (unifSpec.query n) : ProbComp _) (BallotOracleSpec F G)
      pure (u,state)) live) at ho
    rw [runBallotOracle_lift_bind] at ho
    simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,support_bind,support_pure,
      Set.mem_iUnion,Set.mem_singleton_iff] at ho
    obtain ⟨u,hu,rfl⟩ := ho
    rfl
  | inr key =>
    change out ∈ support (runBallotOracle (match state.cache key with
      | some c => pure (c,state)
      | none => do
        let c ← ballotChallengeOracle key.1 key.2
        pure (c,{state with cache := state.cache.cacheQuery key c})) live) at ho
    cases hc : state.cache key with
    | some c =>
      simp [hc,runBallotOracle] at ho
      subst out
      rfl
    | none =>
      simp only [hc,runBallotOracle_bind] at ho
      simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,support_bind,support_pure,
        Set.mem_iUnion,Set.mem_singleton_iff] at ho
      obtain ⟨answer,ha,rfl⟩ := ho
      rfl

omit [Fintype F] [DecidableEq F] in
/-- Raw verification and attacker queries never add or erase honest requests. -/
theorem ballotProgrammed_raw_preserves_requests {α : Type} (g pk : G)
    (oa : BallotOracleComp F G α) (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (α × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp oa (BallotProofOracleSpec F G))).run state) live)) :
    out.1.2.programmed = state.programmed := by
  induction oa using OracleComp.inductionOn generalizing state live with
  | pure x =>
    simp [runBallotOracle] at ho
    subst out
    rfl
  | query_bind t next ih =>
    rw [liftComp_bind,runProgrammed_bind] at ho
    simp only [support_bind,Set.mem_iUnion] at ho
    obtain ⟨head,hh,ho⟩ := ho
    have hq : (simulateQ (ballotProgrammedImpl (F := F) g pk)
        (liftComp (liftM ((BallotOracleSpec F G).query t) : BallotOracleComp F G _)
          (BallotProofOracleSpec F G))).run state = (ballotProgrammedRaw t).run state := by
      cases t with
      | inl n =>
        change (simulateQ (ballotProgrammedImpl (F := F) g pk)
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inl n))))).run state = _
        rw [simulateQ_spec_query]
        rfl
      | inr key =>
        change (simulateQ (ballotProgrammedImpl (F := F) g pk)
          (liftM ((BallotProofOracleSpec F G).query (.inl (.inr key))))).run state = _
        rw [simulateQ_spec_query]
        rfl
    rw [hq] at hh
    exact (ih head.1.1 head.1.2 head.2 ho).trans (programmed_raw_step_list t state live head hh)

omit [Fintype F] in
theorem programmed_submit_accepted (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : ((Decision × List (BoardEntry F G)) × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp (repairedSubmitOracle g pk voter board b) (BallotProofOracleSpec F G))).run state) live))
    (ha : out.1.1.1 = .accepted) :
    b.ExpandedFreshFor (board.map BoardEntry.ballot) ∧ out.1.1.2 = board ++ [⟨voter,b⟩] := by
  simp only [repairedSubmitOracle,liftComp_bind,runProgrammed_bind,support_bind,Set.mem_iUnion] at ho
  obtain ⟨v,hv,ho⟩ := ho
  cases he : v.1.1 <;> simp only [he,Bool.false_eq_true,if_false,if_true] at ho
  · simp only [liftComp_pure,runProgrammed_pure,support_pure,Set.mem_singleton_iff] at ho
    subst out
    contradiction
  · split at ho
    · simp only [liftComp_pure,runProgrammed_pure,support_pure,Set.mem_singleton_iff] at ho
      subst out
      exact ⟨by assumption,rfl⟩
    · simp only [liftComp_pure,runProgrammed_pure,support_pure,Set.mem_singleton_iff] at ho
      subst out
      contradiction

/-- When both actual honest decisions accept, every recorded honest statement
belongs to a covered ciphertext on the returned board, starting with arbitrary
caches and flag and no prior honest programming records. Rejection is retained. -/
theorem repairedCastHonestPairOracle_programmed_targets_from (g pk : G) (vote : Bool)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hempty : state.programmed = [])
    (out : (((Decision × Decision) × List (BoardEntry F G)) × BallotProgrammedState F G) ×
      BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (repairedCastHonestPairOracle g pk vote)).run state) live))
    (ha : out.1.1.1 = (.accepted,.accepted)) :
    ∀ stmt ∈ out.1.2.programmed, ∃ b ∈ out.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = b.coveredStatement g pk i := by
  simp only [repairedCastHonestPairOracle,runProgrammed_bind,
    runProgrammed_pure,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨alice,halice,first,hfirst,bob,hbob,second,hsecond,rfl⟩ := ho
  have ha0 := congrArg Prod.fst ha
  have ha1 := congrArg Prod.snd ha
  have hfirstB := (programmed_submit_accepted g pk 0 [] alice.1.1 _ _ first hfirst ha0).2
  have hsecondB := (programmed_submit_accepted g pk 1 first.1.1.2 bob.1.1 _ _ second hsecond ha1).2
  have haliceL := strongHonestBallotOracle_request_targets g pk vote state live alice halice
  have hfirstL := ballotProgrammed_raw_preserves_requests g pk _ _ _ first hfirst
  have hbobL := strongHonestBallotOracle_request_targets g pk (!vote) _ _ bob hbob
  have hsecondL := ballotProgrammed_raw_preserves_requests g pk _ _ _ second hsecond
  intro stmt hmem
  simp only [hsecondL,hbobL,hfirstL,haliceL,hempty,
    List.append_nil,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hmem
  have hb : second.1.1.2.map BoardEntry.ballot = [alice.1.1,bob.1.1] := by
    simp [hsecondB,hfirstB]
  rcases hmem with (rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact ⟨bob.1.1,by simp [hb],none,rfl⟩
  · exact ⟨bob.1.1,by simp [hb],some 1,rfl⟩
  · exact ⟨bob.1.1,by simp [hb],some 0,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],none,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],some 1,rfl⟩
  · exact ⟨alice.1.1,by simp [hb],some 0,rfl⟩

/-- When both actual honest decisions accept, every recorded honest statement
belongs to a covered ciphertext on the returned board. Rejection is not dropped. -/
theorem repairedCastHonestPairOracle_programmed_targets_of_accepted (g pk : G) (vote : Bool)
    (out : (((Decision × Decision) × List (BoardEntry F G)) × BallotProgrammedState F G) ×
      BallotOracleCache F G)
    (ho : out ∈ support (runBallotProgrammed g pk (repairedCastHonestPairOracle g pk vote)))
    (ha : out.1.1.1 = (.accepted,.accepted)) :
    ∀ stmt ∈ out.1.2.programmed, ∃ b ∈ out.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = b.coveredStatement g pk i := by
  exact repairedCastHonestPairOracle_programmed_targets_from g pk vote .empty ∅ rfl out ho ha

/-- Actual accepted submission after arbitrary raw attacker queries excludes
all recorded honest targets when both prefix decisions accepted. The rejected
prefix case remains a separate probability event, not a freshness assumption. -/
theorem repairedHonestPrefix_accepted_target_exclusion (g pk : G) (vote : Bool)
    (honestRun : (((Decision × Decision) × List (BoardEntry F G)) × BallotProgrammedState F G) ×
      BallotOracleCache F G)
    (hp : honestRun ∈ support (runBallotProgrammed g pk (repairedCastHonestPairOracle g pk vote)))
    (ha : honestRun.1.1.1 = (.accepted,.accepted))
    (attacker : BallotOracleComp F G (Ballot F G 2))
    (made : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (hm : made ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp attacker (BallotProofOracleSpec F G))).run honestRun.1.2) honestRun.2))
    (cast : ((Decision × List (BoardEntry F G)) × BallotProgrammedState F G) × BallotOracleCache F G)
    (hc : cast ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (liftComp (repairedSubmitOracle g pk 2 honestRun.1.1.2 made.1.1)
        (BallotProofOracleSpec F G))).run made.1.2) made.2))
    (haccept : cast.1.1.1 = .accepted) :
    ∀ i, made.1.1.coveredStatement g pk i ∉ cast.1.2.programmed := by
  have hml := ballotProgrammed_raw_preserves_requests g pk attacker _ _ made hm
  have hcl := ballotProgrammed_raw_preserves_requests g pk _ _ _ cast hc
  have hf := (programmed_submit_accepted g pk 2 honestRun.1.1.2 made.1.1 _ _ cast hc haccept).1
  intro i hi
  rw [hcl,hml] at hi
  obtain ⟨old,hold,j,he⟩ := repairedCastHonestPairOracle_programmed_targets_of_accepted
    g pk vote honestRun hp ha _ hi
  exact hf old hold i j (congrArg BallotStatement.ciphertext he)

#print axioms programmed_submit_accepted
#print axioms runProgrammed_bind
#print axioms runProgrammed_pure
#print axioms repairedCastHonestPairOracle_real_eq
#print axioms ballotProgrammed_raw_preserves_requests
#print axioms repairedCastHonestPairOracle_programmed_targets_from
#print axioms repairedCastHonestPairOracle_programmed_targets_of_accepted
#print axioms repairedHonestPrefix_accepted_target_exclusion
end ExplainableCrypto.Helios.Computational
