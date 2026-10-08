import ExplainableCrypto.Helios.Computational.AdaptiveBallotSimulation
import VCVio.OracleComp.SimSemantics.StateT.StateProjection
import VCVio.CryptoFoundations.FiatShamir.QueryBounds

/-! Replayable interpretation of the existing honest-proof simulator. The
shadow cache and requested statements are internal reduction state. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

structure BallotProgrammedState (F G : Type) where
  cache : BallotOracleCache F G
  bad : Bool
  programmed : List (BallotStatement G)

def BallotProgrammedState.toSimState (s : BallotProgrammedState F G) : BallotProofOracleState F G :=
  (s.cache,s.bad)

def BallotProgrammedState.empty : BallotProgrammedState F G := ⟨∅,false,[]⟩

def ballotProgrammedRaw : QueryImpl (BallotOracleSpec F G)
    (StateT (BallotProgrammedState F G) (BallotOracleComp F G)) :=
  QueryImpl.add (spec₁ := unifSpec) (spec₂ := BallotHashSpec F G)
    (fun n s => do
      let u ← liftM ((BallotOracleSpec F G).query (.inl n))
      pure (u,s))
    (fun key s => match s.cache key with
      | some c => pure (c,s)
      | none => do
        let c ← ballotChallengeOracle key.1 key.2
        pure (c,{s with cache := s.cache.cacheQuery key c}))

/-- The existing programming step accepts a complete statement without its
witness. Its live queries, cache policy and sticky flag are unchanged. -/
def ballotProgrammedStatement (stmt : BallotStatement G) :
    StateT (BallotProgrammedState F G) (BallotOracleComp F G) (Proof01 F G) := fun s => do
  let out ← liftComp ((strongBallotSimOracle (F := F) stmt).run s.cache) (BallotOracleSpec F G)
  pure (out.1.1,⟨out.2,s.bad || out.1.2,stmt :: s.programmed⟩)

def ballotProgrammedImpl (g pk : G) : QueryImpl (BallotProofOracleSpec F G)
    (StateT (BallotProgrammedState F G) (BallotOracleComp F G)) :=
  QueryImpl.add (spec₁ := BallotOracleSpec F G) (spec₂ := HonestBallotProofSpec F G)
    ballotProgrammedRaw (fun wit => ballotProgrammedStatement (honestProofStatement g pk wit))

omit [DecidableEq F] in
/-- Exact compatibility of the old witness-indexed request with the exposed
statement step; this is source equality, including all internal state. -/
theorem ballotProgrammedImpl_statement (g pk : G) (wit : BallotWitness F) :
    (ballotProgrammedImpl g pk) (.inr wit) =
      ballotProgrammedStatement (honestProofStatement g pk wit) := rfl

omit [DecidableEq F] in
theorem ballotProgrammedStatement_runtime (stmt : BallotStatement G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((ballotProgrammedStatement (F := F) stmt).run s) live =
      (fun out => ((out.1.1,(⟨out.2,s.bad || out.1.2,stmt :: s.programmed⟩ :
        BallotProgrammedState F G)),live)) <$> (strongBallotSimOracle stmt).run s.cache := by
  change runBallotOracle (do
    let out ← liftComp ((strongBallotSimOracle (F := F) stmt).run s.cache) (BallotOracleSpec F G)
    pure (out.1.1,(⟨out.2,s.bad || out.1.2,stmt :: s.programmed⟩ : BallotProgrammedState F G))) live = _
  rw [runBallotOracle_lift_bind]
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp]

/-- Live queries never disagree with the shadow; differences are confined to
statements actually recorded by honest-proof requests. -/
def BallotProgrammedInv (s : BallotProgrammedState F G) (live : BallotOracleCache F G) : Prop :=
  live ≤ s.cache ∧ ∀ key, key.1 ∉ s.programmed → s.cache key = live key

omit [DecidableEq F] in
/-- Explicit-statement programming preserves the same live/shadow invariant;
the supplied statement, rather than a dummy witness's statement, is recorded. -/
theorem ballotProgrammedStatement_inv (stmt : BallotStatement G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv s live)
    (out : (Proof01 F G × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((ballotProgrammedStatement stmt).run s) live)) :
    BallotProgrammedInv out.1.2 out.2 := by
  rw [ballotProgrammedStatement_runtime,support_map] at ho
  obtain ⟨answer,ha,rfl⟩ := ho
  constructor
  · exact hi.1.trans (strongBallotSimOracle_cache_le stmt s.cache answer ha)
  · intro key hn
    have hn' : key.1 ≠ stmt ∧ key.1 ∉ s.programmed := by simpa using hn
    exact (strongBallotSimOracle_other_statement stmt s.cache answer ha key hn'.1).trans
      (hi.2 key hn'.2)

omit [DecidableEq F] in
/-- Simulation uses private coins and programs the shadow, with no live hashes. -/
theorem ballotProgrammedStatement_query_bound (stmt : BallotStatement G)
    (s : BallotProgrammedState F G) :
    ((ballotProgrammedStatement stmt).run s).IsQueryBoundP (isBallotHashQuery (F := F)) 0 := by
  let : Inhabited F := ⟨0⟩
  have h := FiatShamir.nmaHashQueryBound_liftComp_zero
    (M := BallotStatement G) (Commit := BallotCommitment G) (Chal := F)
    ((strongBallotSimOracle (F := F) stmt).run s.cache)
  have hz : (liftComp ((strongBallotSimOracle (F := F) stmt).run s.cache)
      (BallotOracleSpec F G)).IsQueryBoundP (isBallotHashQuery (F := F)) 0 := by
    apply IsQueryBoundP.of_imp (h := h)
    intro t ht
    cases t <;> simp_all [isBallotHashQuery]
  change (do let out ← liftComp ((strongBallotSimOracle (F := F) stmt).run s.cache) (BallotOracleSpec F G)
             pure (out.1.1,(⟨out.2,s.bad || out.1.2,stmt :: s.programmed⟩ : BallotProgrammedState F G))).IsQueryBoundP _ 0
  simpa only [bind_pure_comp,isQueryBoundP_map_iff] using hz

private def ballotProgrammedCombinedImpl (g pk : G) : QueryImpl (BallotProofOracleSpec F G)
    (StateT (BallotProgrammedState F G × BallotOracleCache F G) ProbComp) :=
  fun t state => (fun out => (out.1.1,(out.1.2,out.2))) <$>
    runBallotOracle (((ballotProgrammedImpl (F := F) g pk) t).run state.1) state.2

omit [DecidableEq F] in
private theorem ballotProgrammed_compose {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run s) live =
      (fun out => ((out.1,out.2.1),out.2.2)) <$>
        (simulateQ (ballotProgrammedCombinedImpl g pk) oa).run (s,live) := by
  apply simulateQ_StateT_StateT_compose (ballotProgrammedImpl g pk) ballotRandomImpl
    (ballotProgrammedCombinedImpl g pk)
  intro t s live
  simp [ballotProgrammedCombinedImpl,Functor.map_map,runBallotOracle]

omit [Field F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem BallotProgrammedInv.empty : BallotProgrammedInv
    (BallotProgrammedState.empty : BallotProgrammedState F G) ∅ := by
  exact ⟨le_rfl,by simp [BallotProgrammedState.empty]⟩

omit [Field F] [DecidableEq F] [SampleableType F] [AddCommGroup G] [Module F G] in
private theorem BallotProgrammedInv.insert {s : BallotProgrammedState F G}
    {live : BallotOracleCache F G} (h : BallotProgrammedInv s live)
    (key : BallotStatement G × BallotCommitment G) (c : F) :
    BallotProgrammedInv {s with cache := s.cache.cacheQuery key c} (live.cacheQuery key c) := by
  constructor
  · intro other d hd
    by_cases he : other = key
    · subst other; simpa using hd
    · simp only [QueryCache.cacheQuery_of_ne _ _ he] at hd ⊢
      exact h.1 hd
  · intro other hn
    by_cases he : other = key
    · subst other; simp
    · simp only [QueryCache.cacheQuery_of_ne _ _ he]
      exact h.2 other hn

omit [DecidableEq F] in
private theorem ballotProgrammedCombined_uniform (g pk : G) (n : Nat)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    ((ballotProgrammedCombinedImpl (F := F) g pk) (.inl (.inl n))).run (s,live) =
      (do let u ← liftM (unifSpec.query n); pure (u,(s,live))) := by
  change (fun out => (out.1.1,(out.1.2,out.2))) <$>
    runBallotOracle (do
      let u ← liftComp (liftM (unifSpec.query n) : ProbComp _) (BallotOracleSpec F G)
      pure (u,s)) live = _
  rw [runBallotOracle_lift_bind]
  simp [runBallotOracle]

omit [DecidableEq F] in
private theorem ballotProgrammedCombined_hash (g pk : G)
    (key : BallotStatement G × BallotCommitment G)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv s live) :
    ((ballotProgrammedCombinedImpl (F := F) g pk) (.inl (.inr key))).run (s,live) =
      (match s.cache key with
      | some c => pure (c,(s,live))
      | none => do
        let c ← uniformSample F
        pure (c,({s with cache := s.cache.cacheQuery key c},live.cacheQuery key c))) := by
  cases hc : s.cache key with
  | some c =>
    have hq : ((ballotProgrammedRaw (F := F) (G := G)) (.inr key)).run s = pure (c,s) := by
      simp [ballotProgrammedRaw,QueryImpl.add,StateT.run,hc]
    change (fun out => (out.1.1,(out.1.2,out.2))) <$>
      runBallotOracle (((ballotProgrammedRaw (F := F) (G := G)) (.inr key)).run s) live = _
    rw [hq]
    simp [runBallotOracle]
  | none =>
    have hl : live key = none := by
      cases hl : live key with
      | none => rfl
      | some c => have h := hi.1 hl; simp [hc] at h
    simp only [ballotProgrammedCombinedImpl,ballotProgrammedImpl,ballotProgrammedRaw,
      QueryImpl.add,StateT.run,hc]
    simp only [runBallotOracle,simulateQ_bind,simulateQ_pure,StateT.run_bind,StateT.run_pure]
    change _ = _
    simp [ballotChallengeOracle,ballotRandomImpl,hl,Functor.map_map]

omit [DecidableEq F] in
private theorem ballotProgrammedCombined_request (g pk : G) (wit : BallotWitness F)
    (s : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    ((ballotProgrammedCombinedImpl (F := F) g pk) (.inr wit)).run (s,live) =
      (do let out ← (strongBallotSimOracle (F := F) (honestProofStatement g pk wit)).run s.cache
          pure (out.1.1,(⟨out.2,s.bad || out.1.2,honestProofStatement g pk wit :: s.programmed⟩,live))) := by
  simp only [ballotProgrammedCombinedImpl,ballotProgrammedImpl,ballotProgrammedStatement,QueryImpl.add,StateT.run]
  rw [runBallotOracle_lift_bind]
  simp [runBallotOracle,Functor.map_map]

omit [DecidableEq F] in
private theorem ballotProgrammed_step_inv (g pk : G) (t : (BallotProofOracleSpec F G).Domain)
    (state : BallotProgrammedState F G × BallotOracleCache F G)
    (hi : BallotProgrammedInv state.1 state.2)
    (out : (BallotProofOracleSpec F G).Range t × (BallotProgrammedState F G × BallotOracleCache F G))
    (ho : out ∈ support (((ballotProgrammedCombinedImpl (F := F) g pk) t).run state)) :
    BallotProgrammedInv out.2.1 out.2.2 := by
  rcases state with ⟨s,live⟩
  cases t with
  | inl t =>
    cases t with
    | inl n =>
      rw [ballotProgrammedCombined_uniform] at ho
      simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
      obtain ⟨_,_,rfl⟩ := ho
      exact hi
    | inr key =>
      rw [ballotProgrammedCombined_hash g pk key s live hi] at ho
      cases hc : s.cache key with
      | some c =>
        simp only [hc,support_pure,Set.mem_singleton_iff] at ho
        subst out; exact hi
      | none =>
        simp only [hc,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
        obtain ⟨c,_,rfl⟩ := ho
        exact hi.insert key c
  | inr wit =>
    rw [ballotProgrammedCombined_request] at ho
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at ho
    obtain ⟨answer,ha,rfl⟩ := ho
    constructor
    · exact hi.1.trans (strongBallotSimOracle_cache_le _ s.cache answer ha)
    · intro key hn
      have hn' : key.1 ≠ honestProofStatement g pk wit ∧ key.1 ∉ s.programmed := by
        simpa using hn
      exact (strongBallotSimOracle_other_statement _ s.cache answer ha key hn'.1).trans
        (hi.2 key hn'.2)

omit [DecidableEq F] in
private theorem ballotProofSim_raw_run (g pk : G) (t : (BallotOracleSpec F G).Domain)
    (s : BallotProofOracleState F G) :
    ((ballotProofSimImpl (F := F) g pk) (.inl t)).run s = (do
      let out ← runBallotOracle (liftM ((BallotOracleSpec F G).query t)) s.1
      pure (out.1,(out.2,s.2))) := by
  simp only [ballotProofSimImpl,ballotProofImpl,QueryImpl.add,runBallotOracle,simulateQ_spec_query]
  rfl

omit [DecidableEq F] in
private theorem ballotProgrammed_step_project (g pk : G) (t : (BallotProofOracleSpec F G).Domain)
    (state : BallotProgrammedState F G × BallotOracleCache F G)
    (hi : BallotProgrammedInv state.1 state.2) :
    Prod.map id (fun s => s.1.toSimState) <$>
      ((ballotProgrammedCombinedImpl (F := F) g pk) t).run state =
        ((ballotProofSimImpl (F := F) g pk) t).run state.1.toSimState := by
  rcases state with ⟨s,live⟩
  cases t with
  | inl t =>
    rw [ballotProofSim_raw_run]
    cases t with
    | inl n =>
      rw [ballotProgrammedCombined_uniform]
      simp [runBallotOracle,ballotRandomImpl,QueryImpl.ofLift_apply,
        BallotProgrammedState.toSimState]
    | inr key =>
      rw [ballotProgrammedCombined_hash g pk key s live hi]
      change _ = (do
        let out ← runBallotOracle (ballotChallengeOracle key.1 key.2) s.cache
        pure (out.1,(out.2,s.bad)))
      rw [runBallotOracle_query]
      cases s.cache key <;> simp [BallotProgrammedState.toSimState]
  | inr wit =>
    rw [ballotProgrammedCombined_request]
    simp [ballotProofSimImpl,ballotProofImpl,QueryImpl.add,StateT.run,
      BallotProgrammedState.toSimState]

/-- Evaluate the replayable adapter using the original lazy ballot oracle. -/
def runBallotProgrammed {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) :
    ProbComp ((α × BallotProgrammedState F G) × BallotOracleCache F G) :=
  runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run .empty) ∅

omit [DecidableEq F] in
/-- The existing runtime projection also applies to reachable intermediate states;
live/shadow consistency is the invariant derived by the enclosing execution. -/
theorem ballotProgrammed_runtime_eq_of_inv {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv state live) :
    (fun out => (out.1.1,out.1.2.toSimState)) <$>
      runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run state) live =
        runBallotProofSim g pk oa state.toSimState := by
  rw [ballotProgrammed_compose]
  have h := map_run_simulateQ_eq_of_query_map_eq_inv'
    (ballotProgrammedCombinedImpl (F := F) g pk) (ballotProofSimImpl (F := F) g pk)
    (fun s => BallotProgrammedInv s.1 s.2) (fun s => s.1.toSimState)
    (fun t s hi out ho => ballotProgrammed_step_inv g pk t s hi out ho)
    (fun t s hi => ballotProgrammed_step_project g pk t s hi)
    oa (state,live) hi
  simpa only [Functor.map_map,Function.comp_def,Prod.map_def,id_eq,runBallotProofSim] using h

omit [DecidableEq F] in
/-- Exact computation equality, including the original shadow cache and sticky
flag. Initialization derives the required invariant. -/
theorem ballotProgrammed_runtime_eq {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) :
    (fun out => (out.1.1,out.1.2.toSimState)) <$> runBallotProgrammed g pk oa =
      runBallotProofSim g pk oa (∅,false) :=
  ballotProgrammed_runtime_eq_of_inv g pk oa .empty ∅ BallotProgrammedInv.empty

omit [DecidableEq F] in
/-- Every supported run has a consistent live cache, and any difference from
the shadow belongs to recorded requests, including after earlier execution. -/
theorem ballotProgrammed_preserves_inv_of_inv {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (hi : BallotProgrammedInv state live)
    (out : (α × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk) oa).run state) live)) :
    BallotProgrammedInv out.1.2 out.2 := by
  rw [ballotProgrammed_compose,support_map] at ho
  obtain ⟨z,hz,rfl⟩ := ho
  exact simulateQ_run_preserves_inv_of_query (ballotProgrammedCombinedImpl g pk)
    (fun s => BallotProgrammedInv s.1 s.2)
    (fun t s hi out ho => ballotProgrammed_step_inv g pk t s hi out ho)
    oa (state,live) hi z hz

omit [DecidableEq F] in
/-- Every supported run has a consistent live cache, and any difference from
the shadow belongs to a statement recorded by actual proof requests. -/
theorem ballotProgrammed_request_provenance {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (out : (α × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotProgrammed g pk oa)) :
    BallotProgrammedInv out.1.2 out.2 := by
  exact ballotProgrammed_preserves_inv_of_inv g pk oa .empty ∅ BallotProgrammedInv.empty out ho

private theorem ballotVerify_cache_agreement (stmt : BallotStatement G) (p : Proof01 F G)
    (cache₁ cache₂ : BallotOracleCache F G)
    (hc : cache₁ (stmt,p.commitment) = cache₂ (stmt,p.commitment)) :
    Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt p) cache₁ =
      Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt p) cache₂ := by
  classical
  have norm (cache : BallotOracleCache F G) :
      Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt p) cache =
        (fun out : F × BallotOracleCache F G => decide (p.Valid (fun _ => out.1) stmt.generator stmt.publicKey stmt.ciphertext))
          <$> runBallotOracle (ballotChallengeOracle stmt p.commitment) cache := by
    simp [runBallotOracle,strongBallotVerifyOracle]
    congr 1
    funext out
    apply Bool.eq_iff_iff.mpr
    simp
  rw [norm cache₁,norm cache₂,runBallotOracle_query,runBallotOracle_query,hc]
  cases cache₂ (stmt,p.commitment) <;> simp

/-- The original full-proof verification agrees outside actual requested statements.
The exclusion premise still has to be derived from the election's decisions. -/
theorem ballotProgrammed_verify_agreement {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α)
    (out : (α × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotProgrammed g pk oa))
    (stmt : BallotStatement G) (p : Proof01 F G) (hn : stmt ∉ out.1.2.programmed) :
    Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt p) out.2 =
      Prod.fst <$> runBallotOracle (strongBallotVerifyOracle stmt p) out.1.2.cache := by
  exact ballotVerify_cache_agreement stmt p _ _
    ((ballotProgrammed_request_provenance g pk oa out ho).2 (stmt,p.commitment) hn).symm

omit [DecidableEq F] in
/-- The replayable adapter issues at most the source hash-or-proof request bound
in live hash queries; simulated proof requests themselves use only uniform coins. -/
theorem ballotProgrammed_query_bound [Fintype F] {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (n : Nat)
    (hb : oa.IsQueryBoundP (growsBallotCache (F := F)) n)
    (s : BallotProgrammedState F G) :
    ((simulateQ (ballotProgrammedImpl g pk) oa).run s).IsQueryBoundP
      (isBallotHashQuery (F := F)) n := by
  let : Inhabited F := ⟨0⟩
  let : IsUniformSpec (BallotHashSpec F G) := IsUniformSpec.ofFintypeInhabited _
  refine hb.simulateQ_run_of_step ?_ ?_ s
  · intro t ht state
    cases t with
    | inl t =>
      cases t with
      | inl k => simp [growsBallotCache] at ht
      | inr key =>
        change IsQueryBoundP (match state.cache key with
          | some c => pure (c,state)
          | none => do
            let c ← ballotChallengeOracle key.1 key.2
            pure (c,{state with cache := state.cache.cacheQuery key c})) _ 1
        cases state.cache key <;>
          simp [ballotChallengeOracle,isBallotHashQuery]
    | inr wit =>
      have h := FiatShamir.nmaHashQueryBound_liftComp_zero
        (M := BallotStatement G) (Commit := BallotCommitment G) (Chal := F)
        ((strongBallotSimOracle (F := F) (honestProofStatement g pk wit)).run state.cache)
      change IsQueryBoundP (do
        let out ← liftComp ((strongBallotSimOracle (F := F)
          (honestProofStatement g pk wit)).run state.cache) (BallotOracleSpec F G)
        pure (out.1.1,(⟨out.2,state.bad || out.1.2,
          honestProofStatement g pk wit :: state.programmed⟩ : BallotProgrammedState F G))) _ 1
      have hzero : (liftComp ((strongBallotSimOracle (F := F)
          (honestProofStatement g pk wit)).run state.cache) (BallotOracleSpec F G)).IsQueryBoundP (isBallotHashQuery (F := F)) 0 := by
        apply IsQueryBoundP.of_imp (h := h)
        intro t ht
        cases t <;> simp_all [isBallotHashQuery]
      simpa only [bind_pure_comp,isQueryBoundP_map_iff] using hzero.mono (show 0 ≤ 1 by omega)
  · intro t ht state
    cases t with
    | inl t =>
      cases t with
      | inl k =>
        simp [ballotProgrammedImpl,ballotProgrammedRaw,QueryImpl.add,StateT.run,
          isBallotHashQuery]
      | inr key => simp [growsBallotCache] at ht
    | inr wit => simp [growsBallotCache] at ht

#print axioms ballotProgrammedImpl_statement
#print axioms ballotProgrammedStatement_runtime
#print axioms ballotProgrammedStatement_inv
#print axioms ballotProgrammedStatement_query_bound
#print axioms ballotProgrammed_runtime_eq_of_inv
#print axioms ballotProgrammed_preserves_inv_of_inv
#print axioms ballotProgrammed_runtime_eq
#print axioms ballotProgrammed_request_provenance
#print axioms ballotProgrammed_verify_agreement
#print axioms ballotProgrammed_query_bound
#print axioms ballotProgrammed_compose
#print axioms ballotProgrammedCombined_uniform
#print axioms ballotProgrammedCombined_hash
#print axioms ballotProgrammedCombined_request
end ExplainableCrypto.Helios.Computational
