import ExplainableCrypto.Helios.Computational.ElectionProgrammedSource

/-! Query-history controls distinguish replayable code from an already
interpreted computation. Literal small-field cases carry no hardness claim. -/
namespace ExplainableCrypto.Helios.Computational.ElectionProgrammedSourceControls
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionProgrammedSource
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
abbrev Scalar := ZMod 11
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar

def statement : BallotStatement Scalar := ⟨1,3,(2,7)⟩
def commitment : BallotCommitment Scalar := ((4,1),(8,2))

noncomputable def fresh : BallotOracleComp Scalar Scalar Scalar :=
  Prod.fst <$> (raw 1 3 (ask (.ballot statement commitment))).run .empty

/-- A fresh raw hash is an actual source query, available to the fork extractor. -/
theorem fresh_eq_query : fresh = ballotChallengeOracle statement commitment := by
  have hq (s : BallotProgrammedState Scalar Scalar) :
      (simulateQ (ballotProgrammedImpl (F := Scalar) 1 3)
        (liftComp (ballotChallengeOracle statement commitment) (BallotProofOracleSpec Scalar Scalar))).run s =
      (ballotProgrammedRaw (.inr (statement,commitment))).run s := by
    change (simulateQ (ballotProgrammedImpl (F := Scalar) 1 3)
      (liftM ((BallotProofOracleSpec Scalar Scalar).query (.inl (.inr (statement,commitment)))))).run s = _
    rw [simulateQ_spec_query]
    rfl
  have hl : (ElectionReplaySource.lower (ask (F := Scalar) (.ballot statement commitment))).run ∅ =
      (do let c ← ballotChallengeOracle statement commitment
          pure (c,(∅ : Cache Scalar Scalar))) := by rfl
  unfold fresh
  change Prod.fst <$> (do
    let out ← (simulateQ (ballotProgrammedImpl (F := Scalar) 1 3)
      (liftComp ((ElectionReplaySource.lower (ask (.ballot statement commitment))).run ∅)
        (BallotProofOracleSpec Scalar Scalar))).run (State.empty : State Scalar Scalar).ballot
    pure (out.1.1,rebuild out.1.2 out.2)) = _
  rw [hl]
  simp only [liftComp_bind,liftComp_pure,simulateQ_bind,StateT.run_bind,simulateQ_pure,StateT.run_pure,hq]
  simp [State.empty,State.ballot,ballotProgrammedRaw,QueryImpl.add,project,StateT.run,monad_norm]


/-- Hiding the evaluated computation would have zero live hash queries; the
actual source cannot satisfy that bound. -/
theorem fresh_not_zero : ¬ fresh.IsQueryBoundP (isBallotHashQuery (F := Scalar)) 0 := by
  rw [fresh_eq_query]
  simp [ballotChallengeOracle,isBallotHashQuery]

noncomputable def hidden : BallotOracleComp Scalar Scalar Scalar :=
  liftComp (uniformSample Scalar) (BallotOracleSpec Scalar Scalar)

/-- Ordinary sampling has the same returned scalar law as the fresh hash query. -/
theorem same_output_law :
    Prod.fst <$> runBallotOracle fresh ∅ = Prod.fst <$> runBallotOracle hidden ∅ := by
  have hh : runBallotOracle hidden ∅ =
      (fun a => (a,(∅ : BallotOracleCache Scalar Scalar))) <$> uniformSample Scalar := by
    have h := runBallotOracle_lift_bind (F := Scalar) (G := Scalar) (uniformSample Scalar)
      (fun a => pure a) (∅ : BallotOracleCache Scalar Scalar)
    simpa only [hidden,bind_pure,runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp] using h
  rw [hh,fresh_eq_query,runBallotOracle_query]
  simp

theorem hidden_zero : hidden.IsQueryBoundP (isBallotHashQuery (F := Scalar)) 0 := by
  have h := FiatShamir.nmaHashQueryBound_liftComp_zero
    (M := BallotStatement Scalar) (Commit := BallotCommitment Scalar) (Chal := Scalar)
    (uniformSample Scalar)
  apply IsQueryBoundP.of_imp (h := h)
  intro t ht
  cases t <;> simp_all [isBallotHashQuery]

/-- Checked counterexample: equality of output laws does not preserve a source
query tree or its available replay locations. -/
theorem same_law_different_source :
    (Prod.fst <$> runBallotOracle fresh ∅ = Prod.fst <$> runBallotOracle hidden ∅) ∧ fresh ≠ hidden := by
  refine ⟨same_output_law,?_⟩
  intro h
  exact fresh_not_zero (h ▸ hidden_zero)

/-- The live-validity theorem includes preparation in both proof domains and
allows the attacker to retain both answers through the election. -/
theorem prepared_live_after_queries
    (adversary : Scalar × Scalar → Adversary Scalar Scalar Scalar)
    (out : ((PublicResult Scalar Scalar × Bool) × State Scalar Scalar) ×
      BallotOracleCache Scalar Scalar)
    (ho : out ∈ support (evaluate (prepared (fun p => p.trusteeKeyProof.response.val) 1
      (do let a ← ask (.key 1 3 4); let b ← ask (.ballot statement commitment); pure (a,b))
      adversary) .empty ∅))
    (hh : out.1.1.1.beforeTally.honestDecisions = (.accepted,.accepted))
    (ha : out.1.1.1.decision = .accepted) :
    out.1.1.1.submission.CachedStrongValid 1 out.1.1.1.beforeTally.parameters.publicKey out.2 :=
  prepared_live _ 1 _ adversary out ho hh ha

/-- Raw computation preserves an incoming foreign record. It cannot be used
as a shortcut for establishing the actual preparation's empty record. -/
theorem foreign_record_survives :
    let cache : Cache Scalar Scalar := (∅ : Cache Scalar Scalar).cacheQuery (.key 1 3 4) 5
    let s : State Scalar Scalar := ⟨cache,true,[statement]⟩
    evaluate (raw 1 3 (pure ())) s (project cache) = pure (((),s),project cache) := by
  let cache : Cache Scalar Scalar := (∅ : Cache Scalar Scalar).cacheQuery (.key 1 3 4) 5
  let s : State Scalar Scalar := ⟨cache,true,[statement]⟩
  change (pure (((),rebuild cache s.ballot),project cache) : ProbComp _) =
    pure (((),s),project cache)
  simp only [rebuild,State.ballot,show s.cache = cache from rfl,replace_project]
  rfl


#print axioms fresh_eq_query
#print axioms fresh_not_zero
#print axioms same_output_law
#print axioms hidden_zero
#print axioms same_law_different_source
#print axioms prepared_live_after_queries
#print axioms foreign_record_survives
end ExplainableCrypto.Helios.Computational.ElectionProgrammedSourceControls
