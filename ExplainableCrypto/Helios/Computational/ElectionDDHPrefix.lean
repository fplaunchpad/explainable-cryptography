import ExplainableCrypto.Helios.Computational.ElectionDDHSource
import ExplainableCrypto.Helios.Computational.ElectionProgrammedExtraction

/-! The actual challenge-only source stops after malicious submission. It keeps
its original callback state and public prefix for finishing after extraction. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (State Source Inv raw trustee evaluate evaluate_bind evaluate_pure)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

structure PrefixResult (F G Init Saved : Type) where
  before : PublicPrefix F G
  submission : Ballot F G 2
  cast : Decision × List (BoardEntry F G)
  saved : Saved
  vote : Bool
  known : Fin 2 → F
  initial : Init

abbrev PrefixOutput (F G Init Saved : Type) := PrefixResult F G Init Saved × State F G

def drawKnown : ProbComp (F × F × F) := do
  let t ← uniformSample F
  let a ← uniformSample F
  let b ← uniformSample F
  pure (t,a,b)

/-- Public challenge inputs suffice for every executed step. The final callback
and trustee publication are deliberately after the retained submission prefix. -/
def preparedPrefix {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Source F G (PrefixResult F G Init Saved) := do
  let initial ← raw g 0 prepare
  let vote ← raw g 0 (liftProb (uniformSample Bool))
  let key ← trustee (TrusteeReachableSimulation.keySim g pk)
  let coins ← raw g pk (liftProb (drawKnown (F := F)))
  let honest ← ballots g pk A T coins.1 coins.2.1 coins.2.2 vote
  let before := ElectionPrefixSimulation.publication fingerprint g pk key honest.1
  let made ← raw g pk ((adversary initial).castBallot before)
  let cast ← raw g pk (liftBallot (repairedSubmitOracle g pk 2 before.board made.1))
  pure ⟨before,made.1,cast,made.2,vote,honest.2,initial⟩

def prefixSource {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    BallotOracleComp F G (PrefixOutput F G Init Saved) :=
  (preparedPrefix fingerprint g pk A T prepare adversary).run .empty

omit [Fintype F] in
/-- The prefix derives consistency from actual empty initialization through
preparation, key simulation, random challenge ballots and malicious submission. -/
theorem prefix_inv {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅)) :
    Inv out.1.2 out.2 := by
  change out ∈ support (evaluate (preparedPrefix fingerprint g pk A T prepare adversary) .empty ∅) at ho
  simp only [preparedPrefix,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,key,hkey,coins,hcoins,honest,hh,made,hm,cast,hcast,rfl⟩ := ho
  have hzero : Inv (State.empty : State F G) ∅ := ⟨le_rfl,by simp [State.empty,State.ballot,project]⟩
  have hii := ElectionProgrammedSource.raw_inv g 0 prepare .empty ∅ hzero initial hi
  have hvi := ElectionProgrammedSource.raw_inv g 0 _ _ _ hii vote hvote
  have hki := ElectionProgrammedSource.key_inv g pk _ _ hvi key hkey
  have hci := ElectionProgrammedSource.raw_inv g pk _ _ _ hki coins hcoins
  have hhi := ballots_inv g pk A T coins.1.1.1 coins.1.1.2.1 coins.1.1.2.2 vote.1.1 _ _ hci honest hh
  have hmi := ElectionProgrammedSource.raw_inv g pk _ _ _ hhi made hm
  exact ElectionProgrammedSource.raw_inv g pk _ _ _ hmi cast hcast

omit [Fintype F] in
/-- The public generator and key are the supplied challenge parameters. -/
theorem prefix_parameters {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅)) :
    out.1.1.before.parameters.generator = g ∧ out.1.1.before.parameters.publicKey = pk := by
  change out ∈ support (evaluate (preparedPrefix fingerprint g pk A T prepare adversary) .empty ∅) at ho
  simp only [preparedPrefix,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,key,hkey,coins,hcoins,honest,hh,made,hm,cast,hcast,rfl⟩ := ho
  exact ⟨rfl,rfl⟩

omit [Fintype F] in
/-- The actual prepared prefix retains the honest column nonce sums even after
arbitrary casting queries and the malicious submission. Both honest decisions
are required; no board-presentation or freshness premise is supplied. -/
theorem prefix_honest_columns {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅))
    (hhonest : out.1.1.before.honestDecisions = (.accepted,.accepted)) (i : Fin 2) :
    boardTally out.1.1.before.board i =
      encryptWith g pk (out.1.1.known i) (if i = 0 then 1 else 0) := by
  change out ∈ support (evaluate (preparedPrefix fingerprint g pk A T prepare adversary) .empty ∅) at ho
  simp only [preparedPrefix,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,key,hkey,coins,hcoins,honest,hh,made,hm,cast,hcast,rfl⟩ := ho
  exact ballots_columns g pk A T coins.1.1.1 coins.1.1.2.1 coins.1.1.2.2 vote.1.1
    _ _ honest hh hhonest i

omit [Fintype F] in
/-- Derive the final board from the actual malicious submission on every
branch. Initialization and every successor supply the needed cache invariant. -/
theorem prefix_cast_board {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅)) :
    out.1.1.cast.2 = if out.1.1.cast.1 = .accepted then
      out.1.1.before.board ++ [⟨2,out.1.1.submission⟩] else out.1.1.before.board := by
  change out ∈ support (evaluate (preparedPrefix fingerprint g pk A T prepare adversary) .empty ∅) at ho
  simp only [preparedPrefix,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,key,hkey,coins,hcoins,honest,hh,made,hm,cast,hcast,rfl⟩ := ho
  have hzero : Inv (State.empty : State F G) ∅ := ⟨le_rfl,by simp [State.empty,State.ballot,ElectionCache.project]⟩
  have hii := ElectionProgrammedSource.raw_inv g 0 prepare .empty ∅ hzero initial hi
  have hvi := ElectionProgrammedSource.raw_inv g 0 _ _ _ hii vote hvote
  have hki := ElectionProgrammedSource.key_inv g pk _ _ hvi key hkey
  have hci := ElectionProgrammedSource.raw_inv g pk _ _ _ hki coins hcoins
  have hhi := ballots_inv g pk A T coins.1.1.1 coins.1.1.2.1 coins.1.1.2.2 vote.1.1 _ _ hci honest hh
  have hmi := ElectionProgrammedSource.raw_inv g pk _ _ _ hhi made hm
  have hr := ElectionProgrammedSource.raw_support g pk _ _ _ hmi cast hcast
  rw [ElectionCache.liftBallot_run,support_map] at hr
  obtain ⟨actual,hactual,he⟩ := hr
  have he' : actual.1 = cast.1.1 := congrArg Prod.fst he
  change cast.1.1.2 = if cast.1.1.1 = .accepted then _ else _
  rw [← he']
  split
  · exact (repairedSubmitOracle_accepted g pk 2 _ _ _ actual hactual (by assumption)).2.2
  · exact repairedSubmitOracle_rejected_preserves_board g pk 2 _ _ _ actual hactual (by assumption)

omit [Fintype F] in
/-- Actual accepted submissions verify in the live cache. Preparation derives
the empty incoming programming record; honest decisions derive target coverage. -/
theorem prefix_live {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅))
    (hhonest : out.1.1.before.honestDecisions = (.accepted,.accepted))
    (haccept : out.1.1.cast.1 = .accepted) :
    out.1.1.submission.CachedStrongValid g pk out.2 := by
  change out ∈ support (evaluate (preparedPrefix fingerprint g pk A T prepare adversary) .empty ∅) at ho
  simp only [preparedPrefix,evaluate_bind,evaluate_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨initial,hi,vote,hvote,key,hkey,coins,hcoins,honest,hh,made,hm,cast,hcast,rfl⟩ := ho
  have hzero : Inv (State.empty : State F G) ∅ := ⟨le_rfl,by simp [State.empty,State.ballot,project]⟩
  have hii := ElectionProgrammedSource.raw_inv g 0 prepare .empty ∅ hzero initial hi
  have hvi := ElectionProgrammedSource.raw_inv g 0 _ _ _ hii vote hvote
  have hki := ElectionProgrammedSource.key_inv g pk _ _ hvi key hkey
  have hci := ElectionProgrammedSource.raw_inv g pk _ _ _ hki coins hcoins
  have hhi := ballots_inv g pk A T coins.1.1.1 coins.1.1.2.1 coins.1.1.2.2 vote.1.1 _ _ hci honest hh
  have hmi := ElectionProgrammedSource.raw_inv g pk _ _ _ hhi made hm
  have hinit := ElectionProgrammedSource.raw_requests g 0 prepare .empty ∅ initial hi
  have hvr := ElectionProgrammedSource.raw_requests g 0 _ _ _ vote hvote
  have hkr := ElectionProgrammedSource.trustee_requests _ _ _ key hkey
  have hcr := ElectionProgrammedSource.raw_requests g pk _ _ _ coins hcoins
  have hempty : coins.1.2.programmed = [] := hcr.trans (hkr.trans (hvr.trans hinit))
  have ht := ballots_targets g pk A T coins.1.1.1 coins.1.1.2.1 coins.1.1.2.2 vote.1.1
    _ _ hempty honest hh hhonest
  have hmr := ElectionProgrammedSource.raw_requests g pk _ _ _ made hm
  have ht' : ∀ stmt ∈ made.1.2.programmed, ∃ old ∈ honest.1.1.1.2.map BoardEntry.ballot,
      ∃ i, stmt = old.coveredStatement g pk i := by simpa only [hmr] using ht
  exact ElectionProgrammedSource.submit_live g pk honest.1.1.1.2 made.1.1.1 _ _ hmi ht' cast hcast haccept

/-- Count actual live queries in preparation, casting and all three submissions.
Key/ballot proof simulation and private sampling make no live hash queries. -/
theorem prefix_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c) :
    (prefixSource fingerprint g pk A T prepare adversary).IsQueryBoundP (isBallotHashQuery (F := F)) (p+c+9) := by
  have h := (ElectionProgrammedExtraction.raw_bound g 0 prepare p hp).bind _ (fun initial =>
    (ElectionProgrammedExtraction.raw_bound g 0 (liftProb (uniformSample Bool)) 0 (ElectionQueryBound.prob_zero _)).bind _ (fun vote =>
    (ElectionProgrammedExtraction.trustee_bound (TrusteeReachableSimulation.keySim (F := F) g pk)).bind _ (fun key =>
    (ElectionProgrammedExtraction.raw_bound g pk (liftProb (drawKnown (F := F))) 0 (ElectionQueryBound.prob_zero _)).bind _ (fun coins : F × F × F =>
    (show ElectionProgrammedExtraction.Bound (ballots (F := F) g pk A T coins.1 coins.2.1 coins.2.2 vote) 6 from
      ballots_bound g pk A T coins.1 coins.2.1 coins.2.2 vote).bind _ (fun honest =>
      let before := ElectionPrefixSimulation.publication fingerprint g pk key honest.1
      (ElectionProgrammedExtraction.raw_bound g pk _ c (hc initial before)).bind _ (fun made =>
      (ElectionProgrammedExtraction.raw_bound g pk _ 3 (ElectionQueryBound.lift_ballot_bound _ 3
        (ElectionQueryBound.submit_bound g pk 2 before.board made.1))).bind _ (fun cast =>
      (show ElectionProgrammedExtraction.Bound (pure (⟨before,made.1,cast,made.2,vote,honest.2,initial⟩ :
        PrefixResult F G Init Saved)) 0 from by intro s; simp))))))))
  simpa only [prefixSource,preparedPrefix,add_zero,zero_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h (State.empty : State F G)

def PrefixAccepted {Init Saved : Type} (out : PrefixOutput F G Init Saved) : Prop :=
  out.1.cast.1 = .accepted ∧ out.1.before.honestDecisions = (.accepted,.accepted)

instance {Init Saved : Type} (out : PrefixOutput F G Init Saved) : Decidable (PrefixAccepted out) :=
  inferInstanceAs (Decidable (_ ∧ _))

def prefixSelect {Init Saved : Type} (g pk : G) (i : Option (Fin 2)) (out : PrefixOutput F G Init Saved) :
    BallotStatement G × Proof01 F G :=
  (out.1.submission.coveredStatement g pk i,
    if PrefixAccepted out then out.1.submission.coveredProof i else replayRejectedProof g)

noncomputable def prefixJoint {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n : Nat) :=
  ballotJointReplay (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk) n

local instance : Inhabited F := ⟨0⟩
noncomputable local instance : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- Success gives three valid witnesses for the same retained original prefix,
including its callback state, known sums and supported actual source execution. -/
theorem prefix_joint_valid {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (n : Nat) (out : PrefixOutput F G Init Saved) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (prefixJoint fingerprint g pk A T prepare adversary n)) :
    PrefixAccepted out ∧
      (∀ i, (out.1.submission.coveredStatement g pk i).Witnesses (w i)) ∧
      (out.1.before.parameters.generator = g ∧ out.1.before.parameters.publicKey = pk) ∧
      ∃ live, (out,live) ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅) := by
  obtain ⟨hv,hs⟩ := ballotJointReplay_valid
    (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk) n out w ho
  have ha : PrefixAccepted out := by
    by_contra hn
    obtain ⟨c,hp⟩ := (hv none).2
    simp only [prefixSelect,if_neg hn,Ballot.coveredStatement] at hp
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)
  obtain ⟨live,hlive⟩ := hs
  exact ⟨ha,fun i => (hv i).1,prefix_parameters fingerprint g pk A T prepare adversary _ hlive,
    live,hlive⟩

/-- Extracted nonces and integer vote counts are consistent across the actual
component and aggregate targets; characteristic two is explicitly excluded. -/
theorem prefix_joint_consistent {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0)
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n : Nat)
    (out : PrefixOutput F G Init Saved) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (prefixJoint fingerprint g pk A T prepare adversary n)) :
    PrefixAccepted out ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    exact one_ne_zero (hg (by simp [he]) : (1 : F) = 0)
  obtain ⟨ha,hw,_⟩ := prefix_joint_valid fingerprint g pk A T hg0 prepare adversary n out w ho
  exact ⟨ha,(out.1.submission.covered_witnesses_sum g pk hg w hw).1,
    out.1.submission.covered_witnesses_atMostOne g pk hg h2 w hw⟩

omit [Fintype F] in
theorem prefix_trace_verified {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (rawOut : PrefixOutput F G Init Saved × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F)
    (hraw : (rawOut.1,ballotForkCacheProject rawOut.2.1) ∈ support
      (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅)) (i : Option (Fin 2)) :
    (ballotForkSourceTrace (prefixSelect g pk i) rawOut).verified = decide (PrefixAccepted rawOut.1) := by
  by_cases ha : PrefixAccepted rawOut.1
  · obtain ⟨c,hcache,hvalid⟩ := prefix_live fingerprint g pk A T prepare adversary
      (rawOut.1,ballotForkCacheProject rawOut.2.1) hraw ha.2 ha.1 i
    have hkey : rawOut.2.1 ((),(prefixSelect g pk i rawOut.1).1,
        (prefixSelect g pk i rawOut.1).2.commitment) = some c := by
      simp only [prefixSelect]
      rw [if_pos ha]
      exact hcache
    rw [show decide (PrefixAccepted rawOut.1) = true from decide_eq_true ha]
    dsimp only [ballotForkSourceTrace]
    rw [hkey]
    dsimp only
    simp only [decide_eq_true_eq]
    exact ⟨True.intro,by simpa [prefixSelect,ha,Ballot.coveredStatement] using hvalid⟩
  · rw [show decide (PrefixAccepted rawOut.1) = false from decide_eq_false ha]
    dsimp only [ballotForkSourceTrace]
    split
    · rfl
    · simp only [decide_eq_false_iff_not]
      rintro ⟨_,hp⟩
      simp only [prefixSelect,if_neg ha,Ballot.coveredStatement] at hp
      exact hg (by simpa [replayRejectedProof,Branch.Valid] using hp.1.1.symm)

/-- Simultaneous replay selection is exactly joint acceptance on this same
original prefix; no correspondence premise or supplied query location remains. -/
theorem prefix_selection_probability {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c) :
    Pr[fun path => ∀ i : Option (Fin 2), (ballotForkSelector (p+c+9) (PFunctor.FreeM.output _
      (ballotReplaySourcePath _ (prefixSelect g pk i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun (prefixSource fingerprint g pk A T prepare adversary))] =
    Pr[fun out => PrefixAccepted out.1 | runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅] :=
  ballotJointReplay_selection_probability (prefixSource fingerprint g pk A T prepare adversary)
    (prefixSelect g pk) (p+c+9) PrefixAccepted (prefix_bound fingerprint g pk A T prepare adversary p c hp hc)
    (prefix_trace_verified fingerprint g pk A T hg prepare adversary)

/-- The actual challenge-only prefix has a joint-extraction bound for one
retained original execution. This is positive success, not negligible failure. -/
theorem prefix_joint_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c) (δ : ENNReal) :
    let a := Pr[fun out => PrefixAccepted out.1 |
      runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅]
    (a - 3*(p+c+9+1 : ENNReal)*δ) * (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | prefixJoint fingerprint g pk A T prepare adversary (p+c+9)] := by
  have h := ballotJointReplay_selection_le (prefixSource fingerprint g pk A T prepare adversary)
    (prefixSelect g pk) (p+c+9) δ
  dsimp only at h ⊢
  rw [prefix_selection_probability fingerprint g pk A T hg prepare adversary p c hp hc] at h
  simpa only [prefixJoint,Nat.cast_add,Nat.cast_ofNat] using h

#print axioms prefix_trace_verified
#print axioms prefix_joint_valid
#print axioms prefix_joint_consistent
#print axioms prefix_selection_probability
#print axioms prefix_joint_le
#print axioms prefix_cast_board
#print axioms prefix_honest_columns
#print axioms prefix_inv
#print axioms prefix_parameters
#print axioms prefix_live
#print axioms prefix_bound
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
