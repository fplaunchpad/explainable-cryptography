import ExplainableCrypto.Helios.Computational.NonzeroSimulationBridge

/-! The full-field simulator is statistically close, but is not exactly the
historical nonzero prover distribution. A zero simulated-branch challenge is
an explicit separating event. This control prevents dropping the 3/|F| loss. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

theorem nonzero_zeroProof_secondChallenge_ne_zero (stmt : BallotStatement G) (nonce : F)
    {t : BallotCommitment G × F × BallotResponse F}
    (ht : t ∈ support ((ballotSigma (F := F) (G := G)).realTranscript stmt (false,nonce))) :
    t.2.1 - t.2.2.1 ≠ 0 := by
  simp only [ChallengeVerifyProtocol.realTranscript, ballotSigma, ballotSigmaWithSampler,
    monad_norm, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ht
  obtain ⟨w, _, e, he, z, _, c, _, rfl⟩ := ht
  simpa [ballotRespondWith] using sampleNonzero_ne_zero he

theorem nonzero_transcript_ne_full_simulator (stmt : BallotStatement G) (nonce : F) :
    𝒮[(ballotSigma (F := F) (G := G)).realTranscript stmt (false,nonce)] ≠
      𝒮[ballotFullSimTranscript stmt] := by
  let t : BallotCommitment G × F × BallotResponse F :=
    (ballotSimCommit (F := F) stmt 0 (0,0,0), 0, (0,0,0))
  have hf : t ∈ support (ballotFullSimTranscript stmt) := by
    simp only [ballotFullSimTranscript, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨0, by simp, 0, by simp, 0, by simp, 0, by simp, rfl⟩
  have hr : t ∉ support ((ballotSigma (F := F) (G := G)).realTranscript stmt (false,nonce)) := by
    intro ht
    exact nonzero_zeroProof_secondChallenge_ne_zero stmt nonce ht (by simp [t])
  intro he
  have hp : Pr[= t | (ballotSigma (F := F) (G := G)).realTranscript stmt (false,nonce)] =
      Pr[= t | ballotFullSimTranscript stmt] := by simp only [probOutput_def, he]
  rw [probOutput_eq_zero_of_not_mem_support hr] at hp
  exact (probOutput_ne_zero_of_mem_support hf) hp.symm

#print axioms nonzero_zeroProof_secondChallenge_ne_zero
#print axioms nonzero_transcript_ne_full_simulator

end ExplainableCrypto.Helios.Computational
