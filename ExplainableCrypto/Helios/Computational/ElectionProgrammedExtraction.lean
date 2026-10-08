import ExplainableCrypto.Helios.Computational.ElectionProgrammedSource
import ExplainableCrypto.Helios.Computational.ElectionQueryBound
import ExplainableCrypto.Helios.Computational.BallotJointReplayBound

/-! Query and rejection accounting for the actual complete programmed source.
The source retains its first public result, winning bit and private state.
DDH challenge construction and polynomial-time adequacy remain separate. -/
namespace ExplainableCrypto.Helios.Computational.ElectionProgrammedExtraction
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionProgrammedSource
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Output (F G : Type) := (PublicResult F G × Bool) × State F G

noncomputable def source {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    BallotOracleComp F G (Output F G) := (prepared fingerprint g prepare adversary).run .empty

def Bound {A : Type} (oa : Source F G A) (n : Nat) : Prop :=
  ∀ s, (oa.run s).IsQueryBoundP (isBallotHashQuery (F := F)) n

omit [DecidableEq F] in
theorem raw_bound {A : Type} (g pk : G) (oa : Comp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) n) : Bound (raw g pk oa) n := by
  intro s
  have hl := ElectionQueryBound.lower_bound oa n hb s.cache
  have h := ballotProgrammed_query_bound g pk _ n (raw_lift_hash_bound _ n hl) s.ballot
  change (do let out ← (simulateQ (ballotProgrammedImpl g pk)
               (liftComp ((ElectionReplaySource.lower oa).run s.cache) (BallotProofOracleSpec F G))).run s.ballot
             pure (out.1.1,rebuild out.1.2 out.2)).IsQueryBoundP _ n
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using h

private theorem ballots_bound (g pk : G) (vote : Bool) : Bound (ballots (F := F) g pk vote) 12 := by
  intro s
  have h := ballotProgrammed_query_bound g pk _ 12
    (repairedCastHonestPairOracle_query_bounds g pk vote).1 s.ballot
  change (do let out ← (simulateQ (ballotProgrammedImpl g pk)
               (repairedCastHonestPairOracle g pk vote)).run s.ballot
             pure (out.1,rebuild s.cache out.2)).IsQueryBoundP _ 12
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using h

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem trustee_bound {A : Type} (step : StateT (Cache F G) ProbComp (A × Bool)) :
    Bound (trustee step) 0 := by
  intro s
  change (do let out ← liftComp (step.run s.cache) (BallotOracleSpec F G)
             pure (out.1.1,(⟨out.2,s.bad || out.1.2,s.programmed⟩ : State F G))).IsQueryBoundP _ 0
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using
    ElectionQueryBound.ballot_prob_zero (G := G) (step.run s.cache)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem Bound.bind {A B : Type} {oa : Source F G A} {n m : Nat}
    (h : Bound oa n) (next : A → Source F G B) (hn : ∀ a, Bound (next a) m) :
    Bound (oa >>= next) (n+m) := by
  intro s
  rw [StateT.run_bind]
  exact isQueryBoundP_bind (h s) (fun out _ => hn out.1 out.2)

/-- Count the actual source tree, including preparation, both callbacks and
all honest/submission phases. Auxiliary proof simulation uses no live hashes. -/
theorem source_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) nc)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) ng) :
    (source fingerprint g prepare adversary).IsQueryBoundP (isBallotHashQuery (F := F))
      (np+nc+ng+15) := by
  have h := (raw_bound g 0 prepare np hp).bind _ (fun initial =>
    (raw_bound g 0 _ 0 (ElectionQueryBound.prob_zero (uniformSample Bool))).bind _ (fun vote =>
    (raw_bound g 0 _ 0 (ElectionQueryBound.prob_zero (sampleNonzero F))).bind _ (fun secret =>
    (trustee_bound (TrusteeReachableSimulation.keySim (F := F) g (secret • g))).bind _ (fun key =>
    (ballots_bound g (secret • g) vote).bind _ (fun honest =>
      let before := ElectionPrefixSimulation.publication fingerprint g (secret • g) key honest
      (raw_bound g (secret • g) _ nc (hc initial before)).bind _ (fun made =>
      (raw_bound g (secret • g) _ 3 (ElectionQueryBound.lift_ballot_bound _ 3
        (ElectionQueryBound.submit_bound g (secret • g) 2 before.board made.1))).bind _ (fun cast =>
      let shares := fun j => partialDecrypt secret (boardTally cast.2 j)
      (trustee_bound (ElectionTrusteeSimulation.simPair g (secret • g) (boardTally cast.2) shares)).bind _ (fun proofs =>
      let view := ElectionTrusteeSimulation.publication before made.1 cast shares proofs
      (raw_bound g (secret • g) _ ng (hh initial made.2 view)).bind _ (fun guess =>
        show Bound (pure (view,decide (guess = vote))) 0 from by intro s; simp)))))))))
  change Bound (prepared fingerprint g prepare adversary) _ at h
  have he : np+(0+(0+(0+(12+(nc+(3+(0+(ng+0)))))))) = np+nc+ng+15 := by omega
  simpa only [source,he] using h .empty

omit [Fintype F] in
private theorem original_finish_before (secret : F) (nonces : Fin 2 → F)
    (before : PublicPrefix F G) (submission : Ballot F G 2) (cache : Cache F G)
    (out : PublicResult F G × Cache F G)
    (ho : out ∈ support (run (finishWithCoins secret nonces before submission) cache)) :
    out.1.beforeTally = before := by
  simp only [finishWithCoins,run_bind,run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨cast,_,p0,_,p1,_,rfl⟩ := ho
  rfl

private theorem original_world_rejection_le {Saved : Type}
    (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g)) (adversary : Adversary F G Saved)
    (vote : Bool) (cache : Cache F G) :
    Pr[fun out => out.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
      run (ElectionExtraction.worldSource fingerprint g adversary vote) cache] ≤
      9 * noncePointBound F := by
  classical
  let after := fun initial : (F × (F × F) × PublicPrefix F G) × Cache F G => run (do
    let made ← adversary.castBallot initial.1.2.2
    let view ← finishWithCoins initial.1.1 ![initial.1.2.1.1,initial.1.2.1.2] initial.1.2.2 made.1
    let guess ← adversary.guessVote made.2 view
    pure (view,guess)) initial.2
  have he : run (ElectionExtraction.worldSource fingerprint g adversary vote) cache =
      run (samplePrefix fingerprint g vote) cache >>= after := by
    rw [ElectionExtraction.worldSource,run_bind]
  rw [he]
  apply le_trans ?_ (samplePrefix_rejection_le fingerprint g hg vote cache)
  rw [probEvent_bind_eq_tsum,probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro initial
  by_cases hh : initial.1.2.2.honestDecisions = (.accepted,.accepted)
  · have hz : Pr[fun out => out.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
        after initial] = 0 := by
      apply probEvent_eq_zero_iff.mpr
      intro out ho hn
      simp only [after,run_bind,run_pure,support_bind,support_pure,
        Set.mem_iUnion,Set.mem_singleton_iff] at ho
      obtain ⟨made,_,view,hview,guess,_,rfl⟩ := ho
      exact hn ((congrArg PublicPrefix.honestDecisions (original_finish_before _ _ _ _ _ view hview)).trans hh)
    simp [hh,hz]
  · rw [if_pos hh]
    exact mul_le_of_le_one_right' probEvent_le_one

/-- The actual original prepared election charges honest rejection to nonce collisions. -/
theorem original_prepared_rejection_le {Init Saved : Type}
    (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Pr[fun out => out.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
      run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅] ≤
      9 * noncePointBound F := by
  rw [ElectionExtraction.preparedSource,run_bind]
  refine probEvent_bind_le_of_forall_le fun initial _ => ?_
  rw [run_bind]
  refine probEvent_bind_le_of_forall_le fun vote _ => ?_
  rw [run_bind]
  simp only [run_pure,bind_pure_comp,probEvent_map,Function.comp_def]
  exact original_world_rejection_le fingerprint g hg (adversary initial.1) vote.1 vote.2

/-- The complete programmed source's honest-rejection event is charged to
historical nonce collisions plus the checked full proof-simulation distance.
No freshness or acceptance premise is imposed on the source distribution. -/
theorem prepared_rejection_le {Init Saved : Type}
    (fingerprint : PublicParameters F G → Nat) (g : G)
    (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c) :
    Pr[fun out => out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
      runBallotOracle (source fingerprint g prepare adversary) ∅] ≤
      9 * noncePointBound F + ENNReal.ofReal ((11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ)) := by
  classical
  let actual := (fun out => ((out.1,false),out.2)) <$>
    run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅
  let simulated := result <$> runBallotOracle (source fingerprint g prepare adversary) ∅
  let rejected : ElectionFullSimulation.Output F G → Bool :=
    fun out => decide (out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted))
  have hd : tvDist actual simulated ≤ (11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by
    change tvDist actual (result <$> evaluate (prepared fingerprint g prepare adversary) .empty ∅) ≤ _
    rw [prepared_runtime_eq]
    exact ElectionFullSimulation.prepared_distance_le fingerprint g hg prepare adversary p c hp hc
  have he := (abs_probOutput_toReal_sub_le_tvDist (rejected <$> actual) (rejected <$> simulated)).trans
    ((tvDist_map_le rejected actual simulated).trans hd)
  simp only [probOutput_map] at he
  have hr : Pr[fun out => rejected out = true | simulated].toReal ≤
      Pr[fun out => rejected out = true | actual].toReal +
        (11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ) := by linarith [(abs_le.mp he).1]
  have hb := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal probEvent_ne_top,ENNReal.ofReal_toReal probEvent_ne_top] at hb
  have ha : Pr[fun out => rejected out = true | actual] ≤ 9 * noncePointBound F := by
    simpa only [actual,rejected,probEvent_map,Function.comp_def,decide_eq_true_eq] using
      original_prepared_rejection_le fingerprint g hg prepare adversary
  have h := hb.trans (add_le_add ha le_rfl)
  simpa only [simulated,rejected,result,probEvent_map,Function.comp_def,decide_eq_true_eq] using h



def Accepted (out : Output F G) : Prop :=
  out.1.1.decision = .accepted ∧ out.1.1.beforeTally.honestDecisions = (.accepted,.accepted)

instance (out : Output F G) : Decidable (Accepted out) := inferInstanceAs (Decidable (_ ∧ _))

def select (g : G) (i : Option (Fin 2)) (out : Output F G) : BallotStatement G × Proof01 F G :=
  (out.1.1.submission.coveredStatement g out.1.1.beforeTally.parameters.publicKey i,
    if Accepted out then out.1.1.submission.coveredProof i else replayRejectedProof g)

noncomputable def joint {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n : Nat) :=
  ballotJointReplay (source fingerprint g prepare adversary) (select g) n

local instance : Inhabited F := ⟨0⟩
noncomputable local instance : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Joint success returns witnesses for one retained original election result,
with actual supported source execution and both honest decisions accepted. -/
theorem joint_valid {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (n : Nat) (out : Output F G) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (joint fingerprint g prepare adversary n)) :
    Accepted out ∧
      (∀ i, (out.1.1.submission.coveredStatement g out.1.1.beforeTally.parameters.publicKey i).Witnesses (w i)) ∧
      ∃ live, (out,live) ∈ support (runBallotOracle (source fingerprint g prepare adversary) ∅) := by
  obtain ⟨hv,hs⟩ := ballotJointReplay_valid (source fingerprint g prepare adversary) (select g) n out w ho
  have ha : Accepted out := by
    by_contra hn
    obtain ⟨c,hp⟩ := (hv none).2
    simp only [select,if_neg hn,Ballot.coveredStatement] at hp
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)
  exact ⟨ha,fun i => (hv i).1,hs⟩

/-- The three witnesses produced by this actual source have consistent nonce
and vote sums; excluding characteristic two gives the historical at-most-one. -/
theorem joint_consistent {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0)
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n : Nat)
    (out : Output F G) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (joint fingerprint g prepare adversary n)) :
    Accepted out ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    exact one_ne_zero (hg (by simp [he]) : (1 : F) = 0)
  obtain ⟨ha,hw,_⟩ := joint_valid fingerprint g hg0 prepare adversary n out w ho
  exact ⟨ha,(out.1.1.submission.covered_witnesses_sum g _ hg w hw).1,
    out.1.1.submission.covered_witnesses_atMostOne g _ hg h2 w hw⟩

private theorem trace_verified {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (raw : Output F G × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (hraw : (raw.1,ballotForkCacheProject raw.2.1) ∈ support
      (runBallotOracle (source fingerprint g prepare adversary) ∅)) (i : Option (Fin 2)) :
    (ballotForkSourceTrace (select g i) raw).verified = decide (Accepted raw.1) := by
  by_cases ha : Accepted raw.1
  · obtain ⟨c,hcache,hvalid⟩ := prepared_live fingerprint g prepare adversary
      (raw.1,ballotForkCacheProject raw.2.1) hraw ha.2 ha.1 i
    have hkey : raw.2.1 ((),(select g i raw.1).1,(select g i raw.1).2.commitment) = some c := by
      simp only [select]
      rw [if_pos ha]
      exact hcache
    rw [show decide (Accepted raw.1) = true from decide_eq_true ha]
    dsimp only [ballotForkSourceTrace]
    rw [hkey]
    dsimp only
    simp only [decide_eq_true_eq]
    exact ⟨True.intro,by simpa [select,ha,Ballot.coveredStatement] using hvalid⟩
  · rw [show decide (Accepted raw.1) = false from decide_eq_false ha]
    dsimp only [ballotForkSourceTrace]
    split
    · rfl
    · simp only [decide_eq_false_iff_not]
      rintro ⟨_,hp⟩
      simp only [select,if_neg ha,Ballot.coveredStatement] at hp
      exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)

/-- Simultaneous selection is exactly accepted submission with both honest
ballots accepted, in the same original complete-source execution. -/
theorem selection_probability {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (np nc ng : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) np)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) nc)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) ng) :
    Pr[fun path => ∀ i : Option (Fin 2), (ballotForkSelector (np+nc+ng+15) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (select g i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun (source fingerprint g prepare adversary))] =
    Pr[fun out => Accepted out.1 | runBallotOracle (source fingerprint g prepare adversary) ∅] := by
  exact ballotJointReplay_selection_probability (source fingerprint g prepare adversary) (select g)
    (np+nc+ng+15) Accepted (source_bound fingerprint g prepare adversary np nc ng hp hc hh)
    (trace_verified fingerprint g hg prepare adversary)

omit [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem ballot_of_hash {A : Type} (oa : Comp F G A) (n : Nat)
    (hb : oa.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) n) :
    oa.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) n := by
  apply IsQueryBoundP.of_imp (h := hb)
  intro t ht
  cases t with
  | inl k => simp [ElectionQueryBound.isBallot] at ht
  | inr key => simp [ElectionCacheBudget.isHash]

/-- The actual joint extraction bound, retaining honest rejection, simulation,
low-context and equal-challenge losses. This is not a DDH secrecy reduction. -/
theorem joint_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c d : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c)
    (hh : ∀ initial saved view, ((adversary initial).guessVote saved view).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) d) (δ : ENNReal) :
    let a := Pr[fun out => out.1.1.1.decision = .accepted |
      runBallotOracle (source fingerprint g prepare adversary) ∅]
    let R := 9 * noncePointBound F + ENNReal.ofReal ((11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ))
    (a - R - 3*((p+c+d+15 : Nat)+1 : ENNReal)*δ) * (δ-(Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | joint fingerprint g prepare adversary (p+c+d+15)] := by
  have hg0 : g ≠ 0 := by
    intro he
    exact one_ne_zero (hg (by simp [he]) : (1 : F) = 0)
  have h := ballotJointReplay_selection_le (source fingerprint g prepare adversary) (select g) (p+c+d+15) δ
  dsimp only at h ⊢
  rw [selection_probability fingerprint g hg0 prepare adversary p c d (ballot_of_hash _ _ hp)
    (fun initial before => ballot_of_hash _ _ (hc initial before))
    (fun initial saved view => ballot_of_hash _ _ (hh initial saved view))] at h
  have hgood : Pr[fun out => out.1.1.1.decision = .accepted |
        runBallotOracle (source fingerprint g prepare adversary) ∅] -
      (9 * noncePointBound F + ENNReal.ofReal ((11*(p : ℝ)+2*c+126) / (Fintype.card F : ℝ))) ≤
      Pr[fun out => Accepted out.1 | runBallotOracle (source fingerprint g prepare adversary) ∅] := by
    apply tsub_le_iff_right.mpr
    apply le_trans ?_ (add_le_add le_rfl (prepared_rejection_le fingerprint g hg prepare adversary p c hp hc))
    apply probEvent_le_add_of_imp_or
    intro out _ ha
    by_cases hh : out.1.1.1.beforeTally.honestDecisions = (.accepted,.accepted)
    · exact Or.inl ⟨ha,hh⟩
    · exact Or.inr hh
  exact (mul_le_mul' (tsub_le_tsub_right hgood _) le_rfl).trans h


#print axioms raw_bound
#print axioms trustee_bound
#print axioms Bound.bind
#print axioms source_bound
#print axioms original_prepared_rejection_le
#print axioms prepared_rejection_le
#print axioms joint_valid
#print axioms joint_consistent
#print axioms selection_probability
#print axioms joint_le
end ExplainableCrypto.Helios.Computational.ElectionProgrammedExtraction
