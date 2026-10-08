import ExplainableCrypto.Helios.Computational.BallotForkSource
import ExplainableCrypto.Helios.Computational.AdaptiveBallotControls

/-! Replay controls using independently derived multiplicative p=23/q=11
fixtures. A real one-query prover has selector probability one; unrelated
traces with the same numeric index need not have matching complete targets. -/
namespace ExplainableCrypto.Helios.Computational.BallotForkControls

open OracleComp OracleSpec StrongBallotOracleControls
noncomputable local instance : SampleableType Scalar := SampleableType.ofFintype Scalar
noncomputable local instance : IsUniformSpec ((Unit →ₒ Scalar) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _
local instance (p : Proof01 Scalar Scalar) (c : Scalar) :
    Decidable (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

def honestProgram : BallotOracleComp Scalar Scalar (BallotStatement Scalar × Proof01 Scalar Scalar) := do
  let p ← strongBallotProofWithCoinsOracle stmt (false,3) (4,2,3)
  pure (stmt,p)

def honestProof (c : Scalar) := ballotTranscriptProof (ballotCommitWith stmt (false,(3 : Scalar)) (4,2,3))
  c (ballotRespondWith (false,3) (4,2,3) c)

def honestTrace (c : Scalar) : BallotForkTrace Scalar Scalar :=
  { forgery := ((),(stmt,(honestProof c).commitment),honestProof c)
    advCache := ∅
    roCache := (∅ : (Unit × BallotForkPoint Scalar →ₒ Scalar).QueryCache).cacheQuery
      ((),stmt,(honestProof c).commitment) c
    queryLog := [((),stmt,(honestProof c).commitment)]
    verified := true }

private theorem honest_valid (c : Scalar) :
    (honestProof c).Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext :=
  ballotTranscript_honest_valid stmt (false,3) (4,2,3) c (by decide)

theorem honest_trace_runtime :
    ballotForkRunTrace honestProgram = (do
      let c ← FiatShamir.Fork.wrappedChallengeQuery Scalar
      pure (honestTrace c)) := by
  rw [ballotForkRunTrace_eq]
  simp only [honestProgram, strongBallotProofWithCoinsOracle, ballotChallengeOracle,
    simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, ballotForkLoggedImpl, QueryImpl.add]
  rw [FiatShamir.Fork.roImpl_run_none Unit _ _ _ (by simp)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro c
  have hv := honest_valid c
  simp only [honestProof] at hv
  simp [honestTrace, honestProof, Proof01.commitment, ballotTranscriptProof] at hv ⊢
  exact hv

theorem honest_selector (c : Scalar) : ballotForkSelector 1 (honestTrace c) = some 0 := by
  simp [ballotForkSelector, FiatShamir.Fork.forkPoint, FiatShamir.Fork.Trace.target,
    honestTrace]

theorem honest_selector_probability_one :
    Pr[fun x => (ballotForkSelector 1 x).isSome | ballotForkRunTrace honestProgram] = 1 := by
  rw [honest_trace_runtime]
  simp [honest_selector]

theorem honest_extraction_probability_le :
    (1 / 2 - 1 / 11 : ENNReal) ≤
      Pr[fun out => out.isSome | ballotForkExtract honestProgram 1] := by
  have h := ballotFork_extraction_probability_le honestProgram 1
  simpa only [honest_selector_probability_one, one_mul, Nat.cast_one,
    one_add_one_eq_two, show Fintype.card Scalar = 11 from rfl, Nat.cast_ofNat, one_div] using h

theorem honest_extraction_probability_positive :
    0 < Pr[fun out => out.isSome | ballotForkExtract honestProgram 1] :=
  lt_of_lt_of_le (by norm_num) honest_extraction_probability_le

theorem literal_replay_extracts_nonce :
    ballotForkExtractPair (honestTrace 5) (honestTrace 6) = (stmt,(false,3)) := by
  norm_num [ballotForkExtractPair, honestTrace, honestProof, ballotExtract,
    ballotRespondWith, ballotTranscriptProof]
  decide

def unrelatedTrace : BallotForkTrace Scalar Scalar :=
  { forgery := ((),(AdaptiveBallotControls.freshStmt,AdaptiveBallotControls.freshPC),
      AdaptiveBallotControls.freshProof)
    advCache := ∅
    roCache := (∅ : (Unit × BallotForkPoint Scalar →ₒ Scalar).QueryCache).cacheQuery
      ((),AdaptiveBallotControls.freshStmt,AdaptiveBallotControls.freshPC) 5
    queryLog := [((),AdaptiveBallotControls.freshStmt,AdaptiveBallotControls.freshPC)]
    verified := true }

theorem same_index_unrelated_targets :
    ballotForkSelector 1 (honestTrace 5) = ballotForkSelector 1 unrelatedTrace ∧
    (honestTrace 5).forgery.2.1 ≠ unrelatedTrace.forgery.2.1 := by decide

def badFullProof : Proof01 Scalar Scalar :=
  { honestProof 5 with one := { (honestProof 5).one with challenge := (honestProof 5).one.challenge+1 } }

theorem unchecked_normalization_loses_rejection :
    ¬ badFullProof.Valid (fun _ => 5) stmt.generator stmt.publicKey stmt.ciphertext ∧
    (ballotTranscriptProof badFullProof.commitment 5
      (badFullProof.zero.challenge,badFullProof.zero.response,badFullProof.one.response)).Valid
        (fun _ => 5) stmt.generator stmt.publicKey stmt.ciphertext := by decide

def fixedUnqueried : BallotOracleComp Scalar Scalar (BallotStatement Scalar × Proof01 Scalar Scalar) :=
  pure (stmt,honestProof 5)

private theorem fixed_valid_iff (c : Scalar) :
    (honestProof 5).Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext ↔ c = 5 := by
  constructor
  · intro hv
    calc c = (honestProof 5).zero.challenge + (honestProof 5).one.challenge := hv.2.2.symm
         _ = 5 := by decide
  · rintro rfl
    exact honest_valid 5

/-- Dropping the verifier query really loses accepted proofs. -/
theorem unqueried_live_only_probability_zero :
    Pr[fun x => (ballotForkSelector 0 x).isSome | ballotForkRunTrace fixedUnqueried] = 0 := by
  rw [ballotForkRunTrace_eq]
  simp [fixedUnqueried, ballotForkSelector, FiatShamir.Fork.forkPoint]

theorem unqueried_verification_probability :
    Pr[fun out => out.1 | runBallotOracle (ballotVerificationGame fixedUnqueried) ∅] =
      1 / 11 := by
  simp only [ballotVerificationGame, fixedUnqueried, pure_bind, strongBallotVerifyOracle,
    runBallotOracle, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  change Pr[fun out => out.1 | (do
    let out ← runBallotOracle (ballotChallengeOracle stmt (honestProof 5).commitment) ∅
    pure (decide ((honestProof 5).Valid (fun _ => out.1) stmt.generator stmt.publicKey stmt.ciphertext),
      out.2))] = _
  rw [runBallotOracle_query]
  simp only [QueryCache.empty_apply]
  simp [fixed_valid_iff]
  have hc : ({x : Scalar | x = 5} : Finset Scalar).card = 1 := by decide
  rw [hc]
  norm_num

theorem completed_unqueried_probability_preserved :
    Pr[fun x => (ballotForkSelector 0 x).isSome |
      ballotForkRunTrace (ballotForkComplete fixedUnqueried)] = 1 / 11 := by
  rw [ballotFork_acceptance_probability_eq fixedUnqueried 0 (by simp [fixedUnqueried])]
  exact unqueried_verification_probability

/-- A one-query honest prover's verifier hits the existing challenge. -/
theorem queried_completion_preserves_trace :
    ballotForkRunTrace (ballotForkComplete honestProgram) = ballotForkRunTrace honestProgram := by
  rw [honest_trace_runtime, ballotForkRunTrace_eq]
  simp only [ballotForkComplete, honestProgram, strongBallotProofWithCoinsOracle,
    ballotChallengeOracle, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, ballotForkLoggedImpl, QueryImpl.add,
    bind_assoc, pure_bind]
  rw [FiatShamir.Fork.roImpl_run_none Unit _ _ _ (by simp)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro c
  have hv := honest_valid c
  simp only [honestProof] at hv
  simp [honestTrace, honestProof, Proof01.commitment, ballotTranscriptProof] at hv ⊢
  exact hv


/-- A source value that may change when the challenge is replayed, while the
cryptographic statement and commitment stay fixed. -/
def taggedProgram : BallotOracleComp Scalar Scalar
    (Bool × (BallotStatement Scalar × Proof01 Scalar Scalar)) :=
  (fun out => (decide (out.2.zero.challenge = 3),out)) <$> honestProgram

theorem tagged_project : Prod.snd <$> taggedProgram = honestProgram := by
  simp [taggedProgram]

theorem tagged_extraction_positive :
    0 < Pr[fun out => out.isSome | ballotForkSourceExtract taggedProgram Prod.snd 1] := by
  rw [ballotForkSourceExtract_probability_eq,tagged_project]
  simpa only [ballotForkExtract,queried_completion_preserves_trace] using
    honest_extraction_probability_positive

/-- Exact same-target valid transcripts need not have the same source tag.
Taking a replay's second source value would change this fixture's tag. -/
theorem replay_can_change_source_tag :
    (honestProof 5).commitment = (honestProof 6).commitment ∧
    (honestProof 5).Valid (fun _ => 5) stmt.generator stmt.publicKey stmt.ciphertext ∧
    (honestProof 6).Valid (fun _ => 6) stmt.generator stmt.publicKey stmt.ciphertext ∧
    decide ((honestProof 5).zero.challenge = 3) ≠
      decide ((honestProof 6).zero.challenge = 3) := by decide

/-- The recovered tag follows the first trace's full proof, even though target
identity alone would allow a different source tag after replay. -/
theorem tagged_first_value
    (path : PFunctor.FreeM.Path (ballotForkRunTrace
      (ballotForkComplete (Prod.snd <$> taggedProgram)))) :
    (ballotForkSourceFirst taggedProgram Prod.snd path).1.1 =
      decide ((PFunctor.FreeM.output _ path).forgery.2.2.zero.challenge = 3) := by
  obtain ⟨cache,hs⟩ := ballotForkSourceFirst_mem taggedProgram Prod.snd path
  simp only [taggedProgram,runBallotOracle,simulateQ_map,StateT.run_map,support_map] at hs
  obtain ⟨out,_,he⟩ := hs
  have htag : (ballotForkSourceFirst taggedProgram Prod.snd path).1.1 =
      decide ((ballotForkSourceFirst taggedProgram Prod.snd path).1.2.2.zero.challenge = 3) := by
    have h : (decide (out.1.2.zero.challenge = 3),out.1) =
        (ballotForkSourceFirst taggedProgram Prod.snd path).1 := congrArg Prod.fst he
    rw [← h]
  have hp := congrArg (fun t : BallotForkTrace Scalar Scalar => t.forgery.2.2)
    (ballotForkSourceFirst_trace taggedProgram Prod.snd path)
  change (ballotForkSourceFirst taggedProgram Prod.snd path).1.2.2 =
    (PFunctor.FreeM.output _ path).forgery.2.2 at hp
  exact htag.trans (congrArg (fun p => decide (p.zero.challenge = 3)) hp)

#print axioms tagged_project
#print axioms tagged_extraction_positive
#print axioms replay_can_change_source_tag
#print axioms tagged_first_value
#print axioms honest_trace_runtime
#print axioms honest_selector_probability_one
#print axioms honest_extraction_probability_positive
#print axioms literal_replay_extracts_nonce
#print axioms same_index_unrelated_targets
#print axioms unchecked_normalization_loses_rejection
#print axioms unqueried_live_only_probability_zero
#print axioms unqueried_verification_probability
#print axioms completed_unqueried_probability_preserved
#print axioms queried_completion_preserves_trace

end ExplainableCrypto.Helios.Computational.BallotForkControls
