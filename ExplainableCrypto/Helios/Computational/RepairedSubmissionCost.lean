import ExplainableCrypto.Helios.Computational.BallotReplayCost
import ExplainableCrypto.Helios.Computational.RepairedSubmissionJoint

/-! Total interaction accounting for the actual repaired source. Scalar sampler
cost is explicit; the canonical finite sampler discharges it. Local computation
and encoded sizes are not charged by this metric. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

private theorem cost_map {ι α β : Type} {spec : OracleSpec ι}
    (oa : OracleComp spec α) (f : α → β) (m : Nat) :
    (f <$> oa).IsTotalQueryBound m ↔ oa.IsTotalQueryBound m :=
  isQueryBound_map_iff oa f m _ _

theorem liftComp_total_query_bound {ι τ α : Type} {spec : OracleSpec ι} (target : OracleSpec τ)
    [MonadLiftT (OracleQuery spec) (OracleQuery target)]
    (oa : OracleComp spec α) (m : Nat) (h : oa.IsTotalQueryBound m) :
    (liftComp oa target).IsTotalQueryBound m := by
  induction oa using OracleComp.inductionOn generalizing m with
  | pure x => trivial
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [liftComp_bind,liftComp_query]
    simp only [OracleQuery.cont_query]
    change (liftM (spec.query t) >>= _ : OracleComp target _).IsTotalQueryBound m
    change 0 < m ∧ ∀ answer, _
    exact ⟨h.1,fun answer => ih _ (m-1) (h.2 _)⟩

/-- Canonical finite sampling uses a single uniform-index query, irrespective
of field cardinality. This statement charges interactions, not index bit length. -/
theorem canonicalSampler_total_query_bound (α : Type) [Fintype α] [Nonempty α] :
    letI := SampleableType.ofFintype α
    (uniformSample α).IsTotalQueryBound 1 := by
  classical
  let : NeZero (Fintype.card α) := ⟨Fintype.card_ne_zero⟩
  have hf (n : Nat) [NeZero n] : (uniformSample (Fin n)).IsTotalQueryBound 1 := by
    cases n with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact ⟨by norm_num,fun _ => trivial⟩
  change ((Fintype.equivFin α).symm <$> uniformSample (Fin (Fintype.card α))).IsTotalQueryBound 1
  exact (cost_map _ _ 1).mpr (hf _)

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]

omit [DecidableEq F] [SampleableType F] in
private theorem nonce_cost : (sampleNonzero F).IsTotalQueryBound 1 := by
  classical
  unfold sampleNonzero
  exact (cost_map _ _ 1).mpr (canonicalSampler_total_query_bound Fˣ)

omit [DecidableEq F] [DecidableEq G] [SampleableType F] in
private theorem honest_cost (g pk : G) (vote : Bool) :
    (strongHonestBallotOracle (F := F) g pk vote).IsTotalQueryBound 5 := by
  have hn : (drawNoncePair F).IsTotalQueryBound 2 := by
    unfold drawNoncePair
    change IsTotalQueryBound _ (1+(1+0))
    apply isTotalQueryBound_bind nonce_cost
    intro r0
    exact isTotalQueryBound_bind nonce_cost (fun _ => trivial)
  unfold strongHonestBallotOracle
  change IsTotalQueryBound _ (2+3)
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ 2 hn)
  intro rs
  unfold strongHonestBallotWithNoncesOracle ballotProofQuery
  exact ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => ⟨by norm_num,fun _ => trivial⟩⟩⟩

omit [SampleableType F] [Fintype F] in
private theorem verify_one_cost (stmt : BallotStatement G) (p : Proof01 F G) :
    (strongBallotVerifyOracle stmt p).IsTotalQueryBound 1 := by
  unfold strongBallotVerifyOracle ballotChallengeOracle
  rw [isTotalQueryBound_query_bind_iff]
  exact ⟨by norm_num,fun _ => trivial⟩

omit [SampleableType F] [Fintype F] in
private theorem verify_cost (g pk : G) (b : Ballot F G 2) :
    (strongBallotVerifyAllOracle g pk b).IsTotalQueryBound 3 := by
  unfold strongBallotVerifyAllOracle
  change IsTotalQueryBound _ (1+2)
  apply isTotalQueryBound_bind (verify_one_cost _ _)
  intro h0
  split
  · trivial
  · change IsTotalQueryBound _ (1+1)
    apply isTotalQueryBound_bind (verify_one_cost _ _)
    intro h1
    split
    · trivial
    · exact verify_one_cost _ _

omit [SampleableType F] [Fintype F] in
theorem repairedSubmitOracle_total_query_bound (g pk : G) (voter : Fin 3)
    (board : List (BoardEntry F G)) (b : Ballot F G 2) :
    (repairedSubmitOracle g pk voter board b).IsTotalQueryBound 3 := by
  unfold repairedSubmitOracle
  change IsTotalQueryBound _ (3+0)
  apply isTotalQueryBound_bind (verify_cost g pk b)
  intro valid
  split
  · split <;> trivial
  · trivial

omit [SampleableType F] in
private theorem prefix_cost (g pk : G) (vote : Bool) :
    (repairedCastHonestPairOracle (F := F) g pk vote).IsTotalQueryBound 16 := by
  unfold repairedCastHonestPairOracle
  change IsTotalQueryBound _ (5+(3+(5+(3+0))))
  apply isTotalQueryBound_bind (honest_cost g pk vote)
  intro alice
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ 3 (repairedSubmitOracle_total_query_bound g pk 0 [] alice))
  intro first
  apply isTotalQueryBound_bind (honest_cost g pk (!vote))
  intro bob
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ 3 (repairedSubmitOracle_total_query_bound g pk 1 first.2 bob))
  intro second
  trivial

omit [SampleableType F] in
/-- Count actual honest nonce/proof requests, raw attacker interactions and all
three original short-circuit verifications before lowering proof requests. -/
theorem repairedSubmissionOracle_total_query_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (m : Nat)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmissionOracle g pk vote attacker).IsTotalQueryBound (m+19) := by
  unfold repairedSubmissionOracle
  rw [show m+19 = 16+(m+(3+0)) by omega]
  apply isTotalQueryBound_bind (prefix_cost g pk vote)
  intro view
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ m (hb view))
  intro ballot
  apply isTotalQueryBound_bind (liftComp_total_query_bound _ _ 3 (repairedSubmitOracle_total_query_bound g pk 2 view.2 ballot))
  intro result
  trivial

omit [DecidableEq F] [Fintype F] in
/-- Four actual scalar draws bound statement simulation on any incoming cache. -/
theorem ballotSim_total_query_bound (stmt : BallotStatement G) (cache : BallotOracleCache F G)
    (hc : (uniformSample F).IsTotalQueryBound 1) :
    ((strongBallotSimOracle (F := F) stmt).run cache).IsTotalQueryBound 4 := by
  have ht : (ballotFullSimTranscript (F := F) stmt).IsTotalQueryBound 4 := by
    unfold ballotFullSimTranscript
    change IsTotalQueryBound _ (1+(1+(1+(1+0))))
    apply isTotalQueryBound_bind hc
    intro c
    apply isTotalQueryBound_bind hc
    intro e
    apply isTotalQueryBound_bind hc
    intro z0
    exact isTotalQueryBound_bind hc (fun _ => trivial)
  unfold strongBallotSimOracle
  change IsTotalQueryBound _ (4+0)
  apply isTotalQueryBound_bind ht
  intro t
  dsimp only
  split <;> trivial

omit [DecidableEq F] [Fintype F] in
private theorem programmed_step_cost (g pk : G)
    (hc : (uniformSample F).IsTotalQueryBound 1)
    (t : (BallotProofOracleSpec F G).Domain) (state : BallotProgrammedState F G) :
    (((ballotProgrammedImpl g pk) t).run state).IsTotalQueryBound 4 := by
  cases t with
  | inl t =>
    cases t with
    | inl k =>
      change IsTotalQueryBound (liftM ((BallotOracleSpec F G).query (.inl k)) >>= _) 4
      rw [isTotalQueryBound_query_bind_iff]
      exact ⟨by norm_num,fun _ => trivial⟩
    | inr key =>
      change IsTotalQueryBound (match state.cache key with
        | some c => pure (c,state)
        | none => do
          let c ← ballotChallengeOracle key.1 key.2
          pure (c,{state with cache := state.cache.cacheQuery key c})) 4
      split
      · trivial
      · unfold ballotChallengeOracle
        rw [isTotalQueryBound_query_bind_iff]
        exact ⟨by norm_num,fun _ => trivial⟩
  | inr wit =>
    change IsTotalQueryBound (do
      let out ← liftComp ((strongBallotSimOracle (F := F)
        (honestProofStatement g pk wit)).run state.cache) (BallotOracleSpec F G)
      pure (out.1.1,(⟨out.2,state.bad || out.1.2,
        honestProofStatement g pk wit :: state.programmed⟩ : BallotProgrammedState F G))) (4+0)
    exact isTotalQueryBound_bind (liftComp_total_query_bound _ _ 4 (ballotSim_total_query_bound _ _ hc)) (fun _ => trivial)

omit [DecidableEq F] [Fintype F] in
theorem ballotProgrammed_total_query_bound {α : Type} (g pk : G)
    (hc : (uniformSample F).IsTotalQueryBound 1)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (m : Nat)
    (h : oa.IsTotalQueryBound m) (state : BallotProgrammedState F G) :
    ((simulateQ (ballotProgrammedImpl g pk) oa).run state).IsTotalQueryBound (4*m) := by
  induction oa using OracleComp.inductionOn generalizing m state with
  | pure x => simp only [simulateQ_pure,StateT.run_pure]; trivial
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [simulateQ_query_bind,StateT.run_bind]
    rw [show 4*m = 4+4*(m-1) by have := h.1; omega]
    apply isTotalQueryBound_bind (programmed_step_cost g pk hc t state)
    intro out
    exact ih out.1 (m-1) (h.2 out.1) out.2

/-- The actual lowered repaired source, with explicit primitive sampler cost.
The conservative factor four charges each source request by the most expensive
handler; honest draws, proof requests and verification are derived. -/
theorem repairedSubmissionSource_total_query_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (m : Nat)
    (hc : (uniformSample F).IsTotalQueryBound 1)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmissionSourceOracle g pk vote attacker).IsTotalQueryBound (4*(m+19)) := by
  unfold repairedSubmissionSourceOracle
  apply (cost_map _ _ _).mpr
  exact ballotProgrammed_total_query_bound g pk hc _ _ (repairedSubmissionOracle_total_query_bound g pk vote attacker m hb) _

attribute [local irreducible] repairedSubmissionSourceOracle

/-- The actual joint extractor inherits a concrete total interaction bound,
including its original execution and all three residual attempts. -/
theorem repairedSubmission_joint_extract_total_query_bound (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n m : Nat)
    (hc : (uniformSample F).IsTotalQueryBound 1)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    (repairedSubmission_joint_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) := by
  have h := ballotJointReplay_total_query_bound (repairedSubmissionSourceOracle g pk vote attacker)
    (repairedSubmissionSelect g pk) (n+15) (4*(m+19))
    (repairedSubmissionSource_total_query_bound g pk vote attacker m hc hb)
  simpa only [repairedSubmission_joint_extract,← Nat.mul_assoc,show 4*4=16 from rfl] using h

/-- Choosing the canonical finite sampler discharges the primitive interaction
cost; no sampler-cost premise remains in this specialization. -/
theorem repairedSubmission_joint_extract_canonical_total_bound (g pk : G) (vote : Bool) :
    letI := SampleableType.ofFintype F
    ∀ (attacker : HonestPrefixView F G → BallotOracleComp F G (Ballot F G 2)) (n m : Nat),
    (∀ view, (attacker view).IsTotalQueryBound m) →
    (repairedSubmission_joint_extract g pk vote attacker n).IsTotalQueryBound (16*(m+19)) := by
  let := SampleableType.ofFintype F
  intro attacker n m hb
  exact repairedSubmission_joint_extract_total_query_bound g pk vote attacker n m
    (canonicalSampler_total_query_bound F) hb

#print axioms ballotSim_total_query_bound
#print axioms liftComp_total_query_bound
#print axioms repairedSubmitOracle_total_query_bound
#print axioms ballotProgrammed_total_query_bound
#print axioms repairedSubmissionSource_total_query_bound
#print axioms repairedSubmission_joint_extract_total_query_bound
#print axioms repairedSubmission_joint_extract_canonical_total_bound
#print axioms canonicalSampler_total_query_bound
#print axioms repairedSubmissionOracle_total_query_bound
end ExplainableCrypto.Helios.Computational
