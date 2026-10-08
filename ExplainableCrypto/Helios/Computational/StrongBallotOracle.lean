import ExplainableCrypto.Helios.Computational.BallotSigma
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.Append

/-! Explicit strong ballot-proof queries, sharing VCVio's lazy random oracle.
The query includes the full statement and commitments. Verification consumes
the original full Proof01, including both branch challenges. -/

namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec

abbrev BallotHashSpec (F G : Type) := (BallotStatement G × BallotCommitment G) →ₒ F
abbrev BallotOracleSpec (F G : Type) := unifSpec + BallotHashSpec F G
abbrev BallotOracleComp (F G : Type) := OracleComp (BallotOracleSpec F G)
abbrev BallotOracleCache (F G : Type) := (BallotHashSpec F G).QueryCache

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def ballotChallengeOracle (stmt : BallotStatement G) (pc : BallotCommitment G) :
    BallotOracleComp F G F :=
  liftM ((BallotOracleSpec F G).query (.inr (stmt,pc)))

def Proof01.commitment (p : Proof01 F G) : BallotCommitment G :=
  ((p.zero.a,p.zero.b),(p.one.a,p.one.b))

def strongBallotProofWithCoinsOracle (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) : BallotOracleComp F G (Proof01 F G) := do
  let pc := ballotCommitWith stmt wit coins
  let c ← ballotChallengeOracle stmt pc
  pure (ballotTranscriptProof pc c (ballotRespondWith wit coins c))

noncomputable def strongBallotProofOracle [Fintype F]
    (stmt : BallotStatement G) (wit : BallotWitness F) : BallotOracleComp F G (Proof01 F G) := do
  let w ← liftComp (sampleNonzero F) _
  let e ← liftComp (sampleNonzero F) _
  let z ← liftComp (sampleNonzero F) _
  strongBallotProofWithCoinsOracle stmt wit (w,e,z)

variable [DecidableEq F] [DecidableEq G]
local instance (hash : Hash F G) (g pk : G) (ct : Ciphertext G) (p : Proof01 F G) :
    Decidable (p.Valid hash g pk ct) := by
  unfold Proof01.Valid Branch.Valid
  infer_instance

def strongBallotVerifyOracle (stmt : BallotStatement G) (p : Proof01 F G) :
    BallotOracleComp F G Bool := do
  let c ← ballotChallengeOracle stmt p.commitment
  pure (decide (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext))

def ballotFunctionImpl (hash : StatementHash F G) : QueryImpl (BallotOracleSpec F G) ProbComp :=
  QueryImpl.ofLift unifSpec ProbComp +
    (fun key => pure (hash key.1.generator key.1.publicKey key.1.ciphertext key.2) :
      QueryImpl (BallotHashSpec F G) ProbComp)

omit [DecidableEq F] [DecidableEq G] in
theorem strongBallotProofWithCoinsOracle_function (hash : StatementHash F G)
    (g pk : G) (v : Bool) (r w e z : F) :
    simulateQ (ballotFunctionImpl hash)
      (strongBallotProofWithCoinsOracle ⟨g,pk,encryptWith g pk r (voteScalar v)⟩ (v,r) (w,e,z)) =
        pure (strongProveVote hash g pk v r w e z) := by
  simp only [strongBallotProofWithCoinsOracle, ballotChallengeOracle, simulateQ_bind,
    simulateQ_spec_query, ballotFunctionImpl, QueryImpl.add_apply_inr, pure_bind, simulateQ_pure]
  congr 1
  exact ballotTranscript_strongProveVote hash g pk v r w e z

omit [DecidableEq F] [DecidableEq G] in
theorem strongBallotProofOracle_function [Fintype F] (hash : StatementHash F G)
    (g pk : G) (v : Bool) (r : F) :
    simulateQ (ballotFunctionImpl hash)
      (strongBallotProofOracle ⟨g,pk,encryptWith g pk r (voteScalar v)⟩ (v,r)) =
      (do
        let w ← sampleNonzero F
        let e ← sampleNonzero F
        let z ← sampleNonzero F
        pure (strongProveVote hash g pk v r w e z)) := by
  simp only [strongBallotProofOracle, simulateQ_bind, liftComp_eq_liftM]
  have hl {α : Type} (oa : ProbComp α) :
      simulateQ (ballotFunctionImpl hash) (liftM oa : BallotOracleComp F G α) = oa := by
    exact (QueryImpl.simulateQ_add_liftM_left _ _ oa).trans (simulateQ_ofLift_eq_self oa)
  simp only [hl, strongBallotProofWithCoinsOracle_function]

theorem strongBallotVerifyOracle_function (hash : StatementHash F G)
    (stmt : BallotStatement G) (p : Proof01 F G) :
    simulateQ (ballotFunctionImpl hash) (strongBallotVerifyOracle stmt p) =
      pure (decide (p.Valid (hash stmt.generator stmt.publicKey stmt.ciphertext)
        stmt.generator stmt.publicKey stmt.ciphertext)) := by
  simp [strongBallotVerifyOracle, ballotChallengeOracle,
    ballotFunctionImpl, Proof01.Valid, Proof01.commitment]

variable [SampleableType F]

def ballotRandomImpl : QueryImpl (BallotOracleSpec F G)
    (StateT (BallotOracleCache F G) ProbComp) :=
  QueryImpl.ofLift unifSpec (StateT (BallotOracleCache F G) ProbComp) +
    (@OracleSpec.randomOracle (BallotStatement G × BallotCommitment G) inferInstance
      (BallotHashSpec F G) (fun _ => ‹SampleableType F›))

def runBallotOracle {α : Type} (oa : BallotOracleComp F G α)
    (cache : BallotOracleCache F G) : ProbComp (α × BallotOracleCache F G) :=
  (simulateQ ballotRandomImpl oa).run cache

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
/-- Sequential raw programs carry their actual final cache into the continuation. -/
theorem runBallotOracle_bind {α β : Type} (oa : BallotOracleComp F G α)
    (next : α → BallotOracleComp F G β) (cache : BallotOracleCache F G) :
    runBallotOracle (oa >>= next) cache = (do
      let out ← runBallotOracle oa cache
      runBallotOracle (next out.1) out.2) := by
  simp only [runBallotOracle,simulateQ_bind,StateT.run_bind]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
theorem runBallotOracle_lift_bind {α β : Type} (oa : ProbComp α)
    (next : α → BallotOracleComp F G β) (cache : BallotOracleCache F G) :
    runBallotOracle (do let x ← liftComp oa _; next x) cache =
      (do let x ← oa; runBallotOracle (next x) cache) := by
  have hl : simulateQ (ballotRandomImpl (F := F) (G := G)) (liftComp oa _) =
      (monadLift oa : StateT (BallotOracleCache F G) ProbComp α) := by
    rw [ballotRandomImpl, QueryImpl.simulateQ_add_liftComp_left]
    change simulateQ ((QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (BallotOracleCache F G) ProbComp)) oa = _
    rw [simulateQ_liftTarget, simulateQ_ofLift_eq_self]
  simp only [runBallotOracle, simulateQ_bind, hl, StateT.run_bind,
    StateT.run_monadLift, monad_norm, monadLift_self]

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
theorem runBallotOracle_query (stmt : BallotStatement G) (pc : BallotCommitment G)
    (cache : BallotOracleCache F G) :
    runBallotOracle (ballotChallengeOracle stmt pc) cache =
      (match cache (stmt,pc) with
      | some c => pure (c,cache)
      | none => do
          let c ← uniformSample F
          pure (c,cache.cacheQuery (stmt,pc) c)) := by
  simp only [runBallotOracle, ballotChallengeOracle, simulateQ_spec_query,
    ballotRandomImpl, QueryImpl.add_apply_inr, randomOracle.run_eq]
  cases cache (stmt,pc) <;> rfl

omit [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] in
theorem runBallotOracle_query_caches (stmt : BallotStatement G) (pc : BallotCommitment G)
    (cache : BallotOracleCache F G) (out : F × BallotOracleCache F G)
    (hout : out ∈ support (runBallotOracle (ballotChallengeOracle stmt pc) cache)) :
    out.2 (stmt,pc) = some out.1 := by
  rw [runBallotOracle_query] at hout
  cases hc : cache (stmt,pc) with
  | some c =>
    simp only [hc, support_pure, Set.mem_singleton_iff] at hout
    subst out
    exact hc
  | none =>
    simp only [hc, support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hout
    obtain ⟨c, _, rfl⟩ := hout
    simp

theorem runBallotOracle_verify_cached (stmt : BallotStatement G) (p : Proof01 F G)
    (cache : BallotOracleCache F G) (c : F)
    (hc : cache (stmt,p.commitment) = some c) :
    runBallotOracle (strongBallotVerifyOracle stmt p) cache =
      pure (decide (p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext), cache) := by
  simp only [runBallotOracle, strongBallotVerifyOracle, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  change (do
    let out ← runBallotOracle (ballotChallengeOracle stmt p.commitment) cache
    pure (decide (p.Valid (fun _ => out.1) stmt.generator stmt.publicKey stmt.ciphertext), out.2)) = _
  rw [runBallotOracle_query, hc]
  simp

omit [DecidableEq F] in
/-- Supported honest proof construction exposes its actual cached challenge
and original full-proof validity for later verification steps. -/
theorem runBallotOracle_honest_cached (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) (hw : stmt.Witnesses wit)
    (cache : BallotOracleCache F G) (out : Proof01 F G × BallotOracleCache F G)
    (hout : out ∈ support (runBallotOracle (strongBallotProofWithCoinsOracle stmt wit coins) cache)) :
    ∃ c, out.2 (stmt,out.1.commitment) = some c ∧
      out.1.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext := by
  simp only [runBallotOracle,strongBallotProofWithCoinsOracle,simulateQ_bind,
    simulateQ_pure,StateT.run_bind,StateT.run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at hout
  obtain ⟨answer,ha,rfl⟩ := hout
  exact ⟨answer.1,runBallotOracle_query_caches stmt (ballotCommitWith stmt wit coins) cache answer ha,
    ballotTranscript_honest_valid stmt wit coins answer.1 hw⟩

theorem runBallotOracle_honest_valid (stmt : BallotStatement G) (wit : BallotWitness F)
    (coins : BallotPrivateCoins F) (hw : stmt.Witnesses wit)
    (cache : BallotOracleCache F G) (out : Proof01 F G × BallotOracleCache F G)
    (hout : out ∈ support (runBallotOracle (strongBallotProofWithCoinsOracle stmt wit coins) cache)) :
    runBallotOracle (strongBallotVerifyOracle stmt out.1) out.2 = pure (true,out.2) := by
  obtain ⟨c,hc,hv⟩ := runBallotOracle_honest_cached stmt wit coins hw cache out hout
  rw [runBallotOracle_verify_cached stmt out.1 out.2 c hc]
  simp [hv]

/-- Actual successful full-proof verification supplies a cached challenge and
validity, including both original branch challenges and their checksum. -/
theorem runBallotOracle_verify_true_cached (stmt : BallotStatement G) (p : Proof01 F G)
    (cache : BallotOracleCache F G) (out : Bool × BallotOracleCache F G)
    (hout : out ∈ support (runBallotOracle (strongBallotVerifyOracle stmt p) cache))
    (ht : out.1 = true) :
    ∃ c, out.2 (stmt,p.commitment) = some c ∧
      p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext := by
  simp only [runBallotOracle,strongBallotVerifyOracle,simulateQ_bind,simulateQ_pure,
    StateT.run_bind,StateT.run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at hout
  obtain ⟨answer,ha,rfl⟩ := hout
  exact ⟨answer.1,runBallotOracle_query_caches stmt p.commitment cache answer ha,of_decide_eq_true ht⟩

omit [Field F] [AddCommGroup G] [Module F G] in
/-- Arbitrary adaptive oracle computations retain every previously supplied answer. -/
theorem runBallotOracle_cache_le {α : Type} (oa : BallotOracleComp F G α)
    (cache : BallotOracleCache F G) (out : α × BallotOracleCache F G)
    (hout : out ∈ support (runBallotOracle oa cache)) : cache ≤ out.2 := by
  apply simulateQ_run_preservesInv ballotRandomImpl (cache ≤ ·) ?_ oa cache le_rfl out hout
  apply QueryImpl.PreservesInv.add
  · intro t cache' hle out' ho
    simp only [QueryImpl.ofLift_apply, StateT.run_monadLift, support_bind, support_pure,
      Set.mem_iUnion, Set.mem_singleton_iff] at ho
    obtain ⟨_, _, rfl⟩ := ho
    exact hle
  · exact QueryImpl.PreservesInv.withCaching_le uniformSampleImpl cache

/-- A proof tied to a cached challenge remains accepted after any adaptive
attacker computation through the same oracle. -/
theorem runBallotOracle_verification_preserved {α : Type} (oa : BallotOracleComp F G α)
    (stmt : BallotStatement G) (p : Proof01 F G) (c : F)
    (cache : BallotOracleCache F G) (out : α × BallotOracleCache F G)
    (hc : cache (stmt,p.commitment) = some c)
    (hv : p.Valid (fun _ => c) stmt.generator stmt.publicKey stmt.ciphertext)
    (hout : out ∈ support (runBallotOracle oa cache)) :
    runBallotOracle (strongBallotVerifyOracle stmt p) out.2 = pure (true,out.2) := by
  rw [runBallotOracle_verify_cached stmt p out.2 c (runBallotOracle_cache_le oa cache out hout hc)]
  simp [hv]

#print axioms strongBallotProofWithCoinsOracle_function
#print axioms strongBallotVerifyOracle_function
#print axioms strongBallotProofOracle_function
#print axioms runBallotOracle_query
#print axioms runBallotOracle_bind
#print axioms runBallotOracle_lift_bind
#print axioms runBallotOracle_verify_cached
#print axioms runBallotOracle_query_caches
#print axioms runBallotOracle_honest_cached
#print axioms runBallotOracle_honest_valid
#print axioms runBallotOracle_verify_true_cached
#print axioms runBallotOracle_cache_le
#print axioms runBallotOracle_verification_preserved

end ExplainableCrypto.Helios.Computational
