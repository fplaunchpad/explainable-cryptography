import ExplainableCrypto.Helios.Computational.ElectionDDHRealSource

/-! Finish the retained original prefix using public inputs and actual replay
witnesses. Bad-event probability and efficiency composition remain separate. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle
open ElectionProgrammedSource (Source raw trustee evaluate)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
local instance finishInhabited : Inhabited F := ⟨0⟩
noncomputable local instance finishUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Rejected ballots contribute no nonce. Missing extraction explicitly falls
back to zero; its correctness is not asserted for an accepted malicious ballot. -/
def extractedShares {Init Saved : Type} (pk : G) (out : PrefixResult F G Init Saved)
    (w : Option (Option (Fin 2) → BallotWitness F)) (i : Fin 2) : G :=
  (out.known i + if out.cast.1 = .accepted then
    match w with | some ws => (ws (some i)).2 | none => 0 else 0) • pk

/-- Public-input finishing retains the actual public records and resumes the
original preparation/casting-dependent guessing callback. No secret is an input. -/
def finishExtracted {Init Saved : Type} (g pk : G) (adversary : Init → Adversary F G Saved)
    (out : PrefixResult F G Init Saved) (w : Option (Option (Fin 2) → BallotWitness F)) :
    Source F G (PublicResult F G × Bool) := do
  let cts := boardTally out.cast.2
  let shares := extractedShares pk out w
  let proofs ← trustee (ElectionTrusteeSimulation.simPair g pk cts shares)
  let view := ElectionTrusteeSimulation.publication out.before out.submission out.cast shares proofs
  let guess ← raw g pk ((adversary out.initial).guessVote out.saved view)
  pure (view,decide (guess = out.vote))

/-- Run extraction and then finish in the original full state and live cache,
including every rejection or extraction-failure output. -/
noncomputable def extractedGame {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n k : Nat) := do
  let out ← simulateQ uniformSampleImpl (prefixRepeated fingerprint g pk A T prepare adversary n k)
  evaluate (finishExtracted g pk adversary out.1.1.1 out.2) out.1.1.2 out.1.2

omit [Fintype F] in
/-- The executed prefix derives correct public-key shares from its retained
board. Witnesses are needed only if the malicious submission was accepted. -/
theorem prefix_extracted_shares {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g A T : G) (secret : F) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅))
    (hh : out.1.1.before.honestDecisions = (.accepted,.accepted))
    (w : Option (Option (Fin 2) → BallotWitness F))
    (hw : out.1.1.cast.1 = .accepted → ∃ ws, w = some ws ∧
      ∀ i, (out.1.1.submission.coveredStatement g (secret • g) (some i)).Witnesses (ws (some i)))
    (i : Fin 2) :
    extractedShares (secret • g) out.1.1 w i = partialDecrypt secret (boardTally out.1.1.cast.2 i) := by
  have hb := prefix_cast_board fingerprint g (secret • g) A T prepare adversary out ho
  have hc := prefix_honest_columns fingerprint g (secret • g) A T prepare adversary out ho hh i
  by_cases ha : out.1.1.cast.1 = .accepted
  · obtain ⟨ws,he,hwitness⟩ := hw ha
    subst w
    have hm := hwitness i
    change out.1.1.submission.ciphertext i =
      encryptWith g (secret • g) (ws (some i)).2 (voteScalar (ws (some i)).1) at hm
    rw [if_pos ha] at hb
    have ht : boardTally out.1.1.cast.2 i = boardTally out.1.1.before.board i + out.1.1.submission.ciphertext i := by
      simp [hb,boardTally]
    rw [ht,hc,hm,encryptWith_add]
    simp [extractedShares,ha,partialDecrypt,encryptWith,smul_smul,mul_comm]
  · rw [if_neg ha] at hb
    rw [hb,hc]
    simp [extractedShares,ha,partialDecrypt,encryptWith,smul_smul,mul_comm]

/-- Exact continuation identity on good retained originals. Extraction success
supplies its own witnesses; rejected malicious ballots require none. The sole
remaining event premise records honest acceptance and no accepted extraction
failure. The probability of its complement must still be charged. -/
theorem extracted_finish_good {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g A T : G) (hg : g ≠ 0) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (n k : Nat)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (w : Option (Option (Fin 2) → BallotWitness F))
    (ho : (out,w) ∈ support (prefixRepeated fingerprint g (secret • g) A T prepare adversary n k))
    (hh : out.1.1.before.honestDecisions = (.accepted,.accepted))
    (hw : out.1.1.cast.1 = .accepted → w.isSome) :
    finishExtracted g (secret • g) adversary out.1.1 w =
      finishAfterCast g (secret • g) secret (adversary out.1.1.initial) out.1.1.vote
        out.1.1.before out.1.1.submission out.1.1.saved out.1.1.cast := by
  have hor : out ∈ support (runBallotOracle
      (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅) := by
    apply (mem_support_iff_of_evalSPMF_eq
      (prefix_repeated_original fingerprint g (secret • g) A T prepare adversary n k) out).mp
    rw [support_map]
    exact ⟨(out,w),ho,rfl⟩
  have hws : out.1.1.cast.1 = .accepted → ∃ ws, w = some ws ∧
      ∀ i, (out.1.1.submission.coveredStatement g (secret • g) (some i)).Witnesses (ws (some i)) := by
    intro ha
    cases w with
    | none => simp at hw; exact False.elim (hw ha)
    | some ws =>
      have hv := prefix_repeated_valid fingerprint g (secret • g) A T hg prepare adversary n k out ws ho
      exact ⟨ws,rfl,fun i => hv.2.1 (some i)⟩
  have hs : extractedShares (secret • g) out.1.1 w =
      fun i => partialDecrypt secret (boardTally out.1.1.cast.2 i) := by
    funext i
    exact prefix_extracted_shares fingerprint g A T secret prepare adversary out hor hh w hws i
  simp only [finishExtracted,hs,finishAfterCast]

omit [Fintype F] [DecidableEq F] in
/-- Every branch publishes the original decision and retained board, including
honest rejection and missing extraction. Shares are the explicit public-input
formula; their correctness on bad branches is not asserted. -/
theorem finishExtracted_publication {Init Saved : Type} (g pk : G)
    (adversary : Init → Adversary F G Saved) (original : PrefixResult F G Init Saved)
    (w : Option (Option (Fin 2) → BallotWitness F)) (s : ElectionProgrammedSource.State F G)
    (live : BallotOracleCache F G)
    (out : ((PublicResult F G × Bool) × ElectionProgrammedSource.State F G) × BallotOracleCache F G)
    (ho : out ∈ support (evaluate (finishExtracted g pk adversary original w) s live)) :
    out.1.1.1.beforeTally = original.before ∧ out.1.1.1.submission = original.submission ∧
      out.1.1.1.decision = original.cast.1 ∧ out.1.1.1.board = original.cast.2 ∧
      out.1.1.1.encryptedTally = boardTally original.cast.2 ∧
      out.1.1.1.decryptionShares = extractedShares pk original w := by
  simp only [finishExtracted,ElectionProgrammedSource.evaluate_bind,ElectionProgrammedSource.evaluate_pure,
    support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨proofs,_,guess,_,rfl⟩ := ho
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Complete-output comparison after actual repeated extraction. Honest
rejection is the actual prefix event, while accepted extraction failure is
bounded explicitly. No witness, board, cache or success-probability premise is
supplied by the caller. This finite bound alone does not prove polynomial time. -/
theorem extracted_finish_distance_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g A T : G) (hg : g ≠ 0) (secret : F) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G Saved) (p c k : Nat)
    (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c) (δ : ENNReal) :
    ENNReal.ofReal (tvDist (extractedGame fingerprint g (secret • g) A T prepare adversary (p+c+9) k)
      (evaluate (completedReal fingerprint g (secret • g) A T secret prepare adversary) .empty ∅)) ≤
      Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
        runBallotOracle (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅] +
        (3*(p+c+9+1 : ENNReal)*δ + (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k) := by
  let mx := simulateQ uniformSampleImpl (prefixRepeated fingerprint g (secret • g) A T prepare adversary (p+c+9) k)
  let finishPublic := fun x : (PrefixOutput F G Init Saved × BallotOracleCache F G) ×
      Option (Option (Fin 2) → BallotWitness F) => evaluate (finishExtracted g (secret • g) adversary x.1.1.1 x.2) x.1.1.2 x.1.2
  let finish := fun out : PrefixOutput F G Init Saved × BallotOracleCache F G =>
    evaluate (finishAfterCast g (secret • g) secret (adversary out.1.1.initial) out.1.1.vote
      out.1.1.before out.1.1.submission out.1.1.saved out.1.1.cast) out.1.2 out.2
  let reject := fun x : (PrefixOutput F G Init Saved × BallotOracleCache F G) ×
      Option (Option (Fin 2) → BallotWitness F) => x.1.1.1.before.honestDecisions ≠ (.accepted,.accepted)
  let failed := fun x : (PrefixOutput F G Init Saved × BallotOracleCache F G) ×
      Option (Option (Fin 2) → BallotWitness F) => PrefixAccepted x.1.1 ∧ x.2 = none
  let bad := fun x => x ∉ support mx ∨ reject x ∨ failed x
  have htv := ofReal_tvDist_bind_left_event_le mx finishPublic (fun x => finish x.1) bad (by
    intro x hx
    simp only [bad,not_or,not_not] at hx
    have hh : x.1.1.1.before.honestDecisions = (.accepted,.accepted) := by simpa [reject] using hx.2.1
    have hw : x.1.1.1.cast.1 = .accepted → x.2.isSome := by
      intro ha
      cases he : x.2 with
      | none => exact False.elim (hx.2.2 ⟨⟨ha,hh⟩,he⟩)
      | some ws => rfl
    have hs := extracted_finish_good fingerprint g A T hg secret prepare adversary (p+c+9) k x.1 x.2 (by simpa only [mx,uniformSampleImpl.support_simulateQ] using hx.1) hh hw
    simp only [finishPublic,finish,hs])
  have hbad : Pr[bad | mx] ≤ Pr[reject | mx] + Pr[failed | mx] :=
    (probEvent_mono (fun x hx hb => hb.elim (fun hn => False.elim (hn hx)) id)).trans
      (probEvent_or_le mx reject failed)
  have hbase : evalSPMF (Prod.fst <$> mx) = evalSPMF (runBallotOracle
      (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅) := by
    simpa only [mx,← simulateQ_map,uniformSampleImpl.evalSPMF_simulateQ] using
      prefix_repeated_original fingerprint g (secret • g) A T prepare adversary (p+c+9) k
  have hrej : Pr[reject | mx] = Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
      runBallotOracle (prefixSource fingerprint g (secret • g) A T prepare adversary) ∅] := by
    have he := probEvent_congr' (p := fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted))
      (fun _ _ => Iff.rfl) hbase
    simpa only [probEvent_map,Function.comp_def,mx,reject] using he
  have hfinish : evalSPMF (mx >>= fun x => finish x.1) = evalSPMF
      (evaluate (completedReal fingerprint g (secret • g) A T secret prepare adversary) .empty ∅) := by
    have he := congrArg (fun law => law >>= fun out => evalSPMF (finish out)) hbase
    simp only [← evalSPMF_bind,bind_map_left] at he
    rw [completedReal,ElectionProgrammedSource.evaluate_bind]
    simpa only [mx,prefixSource,ElectionProgrammedSource.evaluate,finish] using he
  have hfail : Pr[failed | mx] ≤ 3*(p+c+9+1 : ENNReal)*δ + (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k := by
    simpa only [mx,failed,uniformSampleImpl.probEvent_simulateQ] using
      prefix_failure_le fingerprint g (secret • g) A T hg prepare adversary p c k hp hc δ
  have h := htv.trans (hbad.trans (add_le_add le_rfl hfail))
  rw [hrej] at h
  simp only [tvDist,hfinish] at h
  simpa only [extractedGame,mx,finishPublic,tvDist] using h

#print axioms finishExtracted_publication
#print axioms extracted_finish_distance_le
#print axioms prefix_extracted_shares
#print axioms extracted_finish_good
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
