import ExplainableCrypto.Helios.Computational.BallotSigma

/-! Full-field reference transcript simulation. The actual ballotSigma retains
nonzero coins. Exact simulation here is an intermediate result for a statistical
comparison, not a change to the historical prover or a strong-FS security claim. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def ballotSimCommit (stmt : BallotStatement G) (challenge : F) (resp : BallotResponse F) :
    BallotCommitment G :=
  let p₀ := simulatedBranch stmt.generator stmt.publicKey stmt.ciphertext 0 resp.1 resp.2.1
  let p₁ := simulatedBranch stmt.generator stmt.publicKey stmt.ciphertext 1 (challenge-resp.1) resp.2.2
  ((p₀.a,p₀.b),(p₁.a,p₁.b))

theorem ballotCommitWith_eq_simulated (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) (challenge : F) (hw : stmt.Witnesses wit) :
    ballotCommitWith stmt wit coins =
      ballotSimCommit stmt challenge (ballotRespondWith wit coins challenge) := by
  have hv := ballotTranscript_honest_valid stmt wit coins challenge hw
  have hzero := hv.1
  have hone := hv.2.1
  simp only [Branch.Valid, ballotTranscriptProof] at hzero hone
  apply Prod.ext <;> apply Prod.ext
  · exact (eq_sub_iff_add_eq.mpr hzero.1.symm)
  · exact (eq_sub_iff_add_eq.mpr hzero.2.symm)
  · exact (eq_sub_iff_add_eq.mpr hone.1.symm)
  · exact (eq_sub_iff_add_eq.mpr hone.2.symm)

theorem ballotSimCommit_valid (stmt : BallotStatement G) (challenge : F) (resp : BallotResponse F) :
    (ballotTranscriptProof (ballotSimCommit stmt challenge resp) challenge resp).Valid
      (fun _ => challenge) stmt.generator stmt.publicKey stmt.ciphertext := by
  exact ⟨simulatedBranch_valid _ _ _ _ _ _, simulatedBranch_valid _ _ _ _ _ _,
    by simp [ballotTranscriptProof]⟩

variable [DecidableEq F] [DecidableEq G] [SampleableType F]

def ballotFullSimTranscript (stmt : BallotStatement G) :
    ProbComp (BallotCommitment G × F × BallotResponse F) := do
  let c ← uniformSample F
  let e ← uniformSample F
  let z₀ ← uniformSample F
  let z₁ ← uniformSample F
  pure (ballotSimCommit stmt c (e,z₀,z₁), c, (e,z₀,z₁))

/-- Exact HVZK for the full-field reference. No such exact claim is made here
for the historical nonzero prover. -/
theorem ballotSigma_full_hvzk :
    (ballotSigmaWithSampler (G := G) (uniformSample F)).PerfectHVZK ballotFullSimTranscript := by
  intro stmt wit hw
  have hvalid : stmt.Witnesses wit := of_decide_eq_true hw
  apply evalSPMF_ext
  intro t
  trans Pr[= t | do
    let w ← uniformSample F
    let e ← uniformSample F
    let z ← uniformSample F
    let c ← uniformSample F
    let resp := ballotRespondWith wit (w,e,z) c
    pure (ballotSimCommit stmt c resp, c, resp)]
  · simp only [ChallengeVerifyProtocol.realTranscript, ballotSigmaWithSampler, monad_norm]
    apply probOutput_bind_congr
    intro w _
    apply probOutput_bind_congr
    intro e _
    apply probOutput_bind_congr
    intro z _
    apply probOutput_bind_congr
    intro c _
    rw [ballotCommitWith_eq_simulated stmt wit (w,e,z) c hvalid]
  · unfold ballotFullSimTranscript
    vcstep rw under 2
    vcstep rw under 1
    vcstep rw
    vcstep rw under 1
    rcases wit with ⟨vote, nonce⟩
    cases vote
    · apply probOutput_eq_of_relTriple_eqRel (x := t)
      refine relTriple_bind_uniformSample_bij (f := id) (fun c => ?_) Function.bijective_id
      refine relTriple_bind_uniformSample_bij (f := fun e : F => c-e) (fun e => ?_) ?_
      · refine relTriple_bind_uniformSample_bij (f := fun w : F => w + nonce * (c-e))
          (fun w => ?_) (AddGroup.addRight_bijective _)
        refine relTriple_bind_uniformSample_bij (f := id) (fun z => ?_) Function.bijective_id
        exact relTriple_pure_pure rfl
      · constructor
        · intro x y h
          simpa using congrArg (fun a => c-a) h
        · intro x
          exact ⟨c-x, by simp⟩
    · vcstep rw under 2
      apply probOutput_eq_of_relTriple_eqRel (x := t)
      refine relTriple_bind_uniformSample_bij (f := id) (fun c => ?_) Function.bijective_id
      refine relTriple_bind_uniformSample_bij (f := id) (fun e => ?_) Function.bijective_id
      refine relTriple_bind_uniformSample_bij (f := id) (fun z => ?_) Function.bijective_id
      refine relTriple_bind_uniformSample_bij (f := fun w : F => w + nonce * (c-e))
        (fun w => ?_) (AddGroup.addRight_bijective _)
      exact relTriple_pure_pure rfl

#print axioms ballotCommitWith_eq_simulated
#print axioms ballotSimCommit_valid
#print axioms ballotSigma_full_hvzk

end ExplainableCrypto.Helios.Computational
