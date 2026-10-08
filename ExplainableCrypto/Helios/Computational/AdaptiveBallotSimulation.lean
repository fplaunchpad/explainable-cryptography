import ExplainableCrypto.Helios.Computational.BallotOracleBudget

/-! Multiple honest proofs interleaved with adaptive hash queries. Proof requests
are internal challenger calls carrying a bit and nonce; only the proof is returned.
The shared oracle state retains the cache and an internal sticky collision flag.
This interface supplies simulation, not extraction of adversarial ballots. -/
namespace ExplainableCrypto.Helios.Computational

open OracleComp OracleSpec
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev HonestBallotProofSpec (F G : Type) := (Bool × F) →ₒ Proof01 F G
abbrev BallotProofOracleSpec (F G : Type) := BallotOracleSpec F G + HonestBallotProofSpec F G
abbrev BallotProofOracleState (F G : Type) := BallotOracleCache F G × Bool

def honestProofStatement (g pk : G) (wit : BallotWitness F) : BallotStatement G :=
  ⟨g,pk,encryptWith g pk wit.2 (voteScalar wit.1)⟩

def ballotProofQuery (wit : BallotWitness F) : OracleComp (BallotProofOracleSpec F G) (Proof01 F G) :=
  liftM ((BallotProofOracleSpec F G).query (.inr wit))

def isBallotProofRequest : (BallotProofOracleSpec F G).Domain → Prop
  | .inl _ => False
  | .inr _ => True

def growsBallotCache : (BallotProofOracleSpec F G).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr _) => True
  | .inr _ => True

instance : DecidablePred (isBallotProofRequest (F := F) (G := G)) := fun key =>
  match key with
  | .inl _ => inferInstanceAs (Decidable False)
  | .inr _ => inferInstanceAs (Decidable True)

instance : DecidablePred (growsBallotCache (F := F) (G := G)) := fun key =>
  match key with
  | .inl (.inl _) => inferInstanceAs (Decidable False)
  | .inl (.inr _) => inferInstanceAs (Decidable True)
  | .inr _ => inferInstanceAs (Decidable True)

def ballotProofImpl (step : BallotWitness F →
    StateT (BallotOracleCache F G) ProbComp (Proof01 F G × Bool)) :
    QueryImpl (BallotProofOracleSpec F G) (StateT (BallotProofOracleState F G) ProbComp) :=
  QueryImpl.add (m := StateT (BallotProofOracleState F G) ProbComp)
  (spec₁ := BallotOracleSpec F G) (spec₂ := HonestBallotProofSpec F G)
  (fun t state => do
    let out ← (ballotRandomImpl (F := F) (G := G) t).run state.1
    pure (out.1,(out.2,state.2)) :
    QueryImpl (BallotOracleSpec F G) (StateT (BallotProofOracleState F G) ProbComp))
  (fun wit state => do
    let out ← (step wit).run state.1
    pure (out.1.1,(out.2,state.2 || out.1.2)) :
    QueryImpl (HonestBallotProofSpec F G) (StateT (BallotProofOracleState F G) ProbComp))

noncomputable def ballotProofRealImpl (g pk : G) :=
  ballotProofImpl (F := F) (fun wit => strongBallotRealOracle (honestProofStatement g pk wit) wit)

def ballotProofSimImpl (g pk : G) :=
  ballotProofImpl (F := F) (fun wit => strongBallotSimOracle (honestProofStatement g pk wit))

noncomputable def runBallotProofReal {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (state : BallotProofOracleState F G) :=
  (simulateQ (ballotProofRealImpl (F := F) g pk) oa).run state

def runBallotProofSim {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (state : BallotProofOracleState F G) :=
  (simulateQ (ballotProofSimImpl (F := F) g pk) oa).run state

omit [Fintype F] [DecidableEq F] in
private theorem simStep_cache_bound (g pk : G) (t : (BallotProofOracleSpec F G).Domain)
    (state : BallotProofOracleState F G) (k : Nat) (hc : BallotCacheBound state.1 k)
    (out : (BallotProofOracleSpec F G).Range t × BallotProofOracleState F G)
    (ho : out ∈ support (((ballotProofSimImpl (F := F) g pk) t).run state)) :
    BallotCacheBound out.2.1 (k + if growsBallotCache t then 1 else 0) := by
  cases t with
  | inl t =>
    simp only [ballotProofSimImpl, ballotProofImpl, QueryImpl.add, StateT.run,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho
    obtain ⟨answer,ha,rfl⟩ := ho
    cases t with
    | inl u =>
      change answer ∈ support (((ballotRandomImpl (F := F) (G := G)) (.inl u)).run state.1) at ha
      simp only [ballotRandomImpl, QueryImpl.add_apply_inl, QueryImpl.ofLift_apply,
        StateT.run_monadLift, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at ha
      obtain ⟨_,_,rfl⟩ := ha
      simpa [growsBallotCache] using hc
    | inr key =>
      have hb : IsQueryBoundP
          (liftM ((BallotOracleSpec F G).query (.inr key)) : BallotOracleComp F G F)
          (isBallotHashQuery (F := F)) 1 := by
        simp [isQueryBoundP_query_iff, isBallotHashQuery]
      have h := runBallotOracle_cache_bound _ 1 k hb state.1 hc answer
        (by simpa only [runBallotOracle, simulateQ_spec_query, StateT.run] using ha)
      simpa [growsBallotCache] using h
  | inr wit =>
    simp only [ballotProofSimImpl, ballotProofImpl, QueryImpl.add, StateT.run,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho
    obtain ⟨answer,ha,rfl⟩ := ho
    simpa [growsBallotCache] using strongBallotSimOracle_cache_bound
      (honestProofStatement g pk wit) state.1 k hc answer ha

omit [Fintype F] [DecidableEq F] in
/-- Supported adaptive simulation grows the ballot cache by at most its hash
and proof-request budget. This supplies the successor cover for the full election. -/
theorem runBallotProofSim_cache_bound {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (n k : Nat)
    (hb : oa.IsQueryBoundP growsBallotCache n)
    (state : BallotProofOracleState F G) (hc : BallotCacheBound state.1 k)
    (out : α × BallotProofOracleState F G)
    (ho : out ∈ support (runBallotProofSim g pk oa state)) :
    BallotCacheBound out.2.1 (k+n) := by
  induction oa using OracleComp.inductionOn generalizing n k state with
  | pure x =>
    simp only [runBallotProofSim,simulateQ_pure,StateT.run_pure,support_pure,
      Set.mem_singleton_iff] at ho
    subst out
    exact hc.mono (Nat.le_add_right _ _)
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hb
    simp only [runBallotProofSim,simulateQ_bind,simulateQ_spec_query,StateT.run_bind,
      support_bind,Set.mem_iUnion] at ho
    obtain ⟨answer,ha,ho⟩ := ho
    have hcache := simStep_cache_bound g pk t state k hc answer ha
    have h := ih answer.1 _ _ (hb.2 answer.1) answer.2 hcache ho
    apply h.mono
    by_cases ht : growsBallotCache t
    · have : 0 < n := hb.1.resolve_left (not_not.mpr ht)
      simp only [ht,ite_true]
      omega
    · simp [ht]

private theorem real_sim_step_distance (g pk : G)
    (hg : Function.Injective (fun r : F => r • g))
    (t : (BallotProofOracleSpec F G).Domain) (state : BallotProofOracleState F G)
    (k : Nat) (hc : BallotCacheBound state.1 k) :
    tvDist (((ballotProofRealImpl (F := F) g pk) t).run state)
      (((ballotProofSimImpl (F := F) g pk) t).run state) ≤
        if isBallotProofRequest t then (3 + (k : ℝ)) * (Fintype.card F : ℝ)⁻¹ else 0 := by
  cases t with
  | inl t => simp [ballotProofRealImpl, ballotProofSimImpl, ballotProofImpl, QueryImpl.add, isBallotProofRequest]
  | inr wit =>
    let f : (Proof01 F G × Bool) × BallotOracleCache F G →
        Proof01 F G × BallotProofOracleState F G := fun out => (out.1.1,(out.2,state.2 || out.1.2))
    have hmap := tvDist_map_le f
      ((strongBallotRealOracle (honestProofStatement g pk wit) wit).run state.1)
      ((strongBallotSimOracle (F := F) (honestProofStatement g pk wit)).run state.1)
    have hstep := strongBallot_programming_step_of_cache_bound (honestProofStatement g pk wit)
      wit rfl hg state.1 k hc
    simpa only [ballotProofRealImpl, ballotProofSimImpl, ballotProofImpl, QueryImpl.add,
      StateT.run, map_eq_bind_pure_comp, Function.comp_def, f, isBallotProofRequest,
      ite_true, add_mul] using hmap.trans hstep

/-- Adaptive honest-proof simulation, including final cache and sticky bad flag.
The program can choose later requests from earlier proofs/hash answers. This
does not extract witnesses from adversarial proofs or prove election secrecy. -/
theorem strongBallot_programming_distance_le {α : Type} (g pk : G)
    (hg : Function.Injective (fun r : F => r • g))
    (oa : OracleComp (BallotProofOracleSpec F G) α) (n p k : Nat)
    (hn : oa.IsQueryBoundP growsBallotCache n)
    (hp : oa.IsQueryBoundP isBallotProofRequest p)
    (state : BallotProofOracleState F G) (hc : BallotCacheBound state.1 k) :
    tvDist (runBallotProofReal g pk oa state) (runBallotProofSim g pk oa state) ≤
      (p : ℝ) * (3 + (k+n : Nat)) * (Fintype.card F : ℝ)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing n p k state with
  | pure x =>
    simp only [runBallotProofReal, runBallotProofSim, simulateQ_pure, StateT.run_pure,
      tvDist_self]
    positivity
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hn hp
    let n' := if growsBallotCache t then n-1 else n
    let p' := if isBallotProofRequest t then p-1 else p
    let cost := if growsBallotCache t then 1 else 0
    let base : ℝ := (3 + (k+n : Nat)) * (Fintype.card F : ℝ)⁻¹
    have hsize : k+cost+n' ≤ k+n := by
      by_cases ht : growsBallotCache t
      · have : 0 < n := hn.1.resolve_left (not_not.mpr ht)
        simp only [cost, n', ht, ite_true]
        omega
      · simp [cost, n', ht]
    let realStep := ((ballotProofRealImpl (F := F) g pk) t).run state
    let simStep := ((ballotProofSimImpl (F := F) g pk) t).run state
    let realNext := fun out : (BallotProofOracleSpec F G).Range t × BallotProofOracleState F G =>
      runBallotProofReal g pk (next out.1) out.2
    let simNext := fun out : (BallotProofOracleSpec F G).Range t × BallotProofOracleState F G =>
      runBallotProofSim g pk (next out.1) out.2
    have hcont : tvDist (simStep >>= realNext) (simStep >>= simNext) ≤ (p' : ℝ) * base := by
      apply tvDist_bind_left_le_const
      intro out ho
      have hcache := simStep_cache_bound g pk t state k hc out ho
      have h := ih out.1 n' p' (k+cost) (hn.2 out.1) (hp.2 out.1) out.2 hcache
      apply h.trans
      dsimp [base]
      rw [← mul_assoc]
      gcongr
    have hstep := real_sim_step_distance g pk hg t state k hc
    have hfirst := (tvDist_bind_right_le realNext realStep simStep).trans hstep
    have hsum : (if isBallotProofRequest t then
        (3+(k : ℝ)) * (Fintype.card F : ℝ)⁻¹ else 0) + (p' : ℝ) * base ≤ (p : ℝ) * base := by
      by_cases ht : isBallotProofRequest t
      · have hpos : 0 < p := hp.1.resolve_left (not_not.mpr ht)
        have hpc : (p' : ℝ) + 1 = (p : ℝ) := by
          exact_mod_cast (show p' + 1 = p by simp only [p',ht,ite_true]; omega)
        have hsmall : (3+(k : ℝ)) * (Fintype.card F : ℝ)⁻¹ ≤ base := by
          dsimp [base]
          gcongr
          exact_mod_cast Nat.le_add_right k n
        simp only [ht,ite_true]
        calc _ ≤ base + (p' : ℝ) * base := add_le_add hsmall le_rfl
             _ = (p : ℝ) * base := by rw [← hpc]; ring
      · simp [ht,p']
    simp only [runBallotProofReal, runBallotProofSim, simulateQ_bind, simulateQ_spec_query,
      StateT.run_bind]
    change tvDist (realStep >>= realNext) (simStep >>= simNext) ≤ _
    exact (tvDist_triangle _ _ _).trans ((add_le_add hfirst hcont).trans
      (by simpa only [base, mul_assoc] using hsum))

omit [DecidableEq F] in
/-- An honest request runs the existing historical constructor and runtime;
the internal flag is unchanged on the real side. -/
theorem runBallotProofReal_request (g pk : G) (wit : BallotWitness F)
    (state : BallotProofOracleState F G) :
    runBallotProofReal g pk (ballotProofQuery wit) state =
      (do
        let out ← runBallotOracle (strongBallotProofOracle (honestProofStatement g pk wit) wit) state.1
        pure (out.1,(out.2,state.2))) := by
  simp [runBallotProofReal, ballotProofQuery, ballotProofRealImpl, ballotProofImpl,
    QueryImpl.add, strongBallotRealOracle, StateT.run, monad_norm]

omit [Fintype F] [DecidableEq F] in
theorem runBallotProofSim_request (g pk : G) (wit : BallotWitness F)
    (state : BallotProofOracleState F G) :
    runBallotProofSim g pk (ballotProofQuery wit) state =
      (do
        let out ← (strongBallotSimOracle (F := F) (honestProofStatement g pk wit)).run state.1
        pure (out.1.1,(out.2,state.2 || out.1.2))) := by
  simp [runBallotProofSim, ballotProofQuery, ballotProofSimImpl, ballotProofImpl,
    QueryImpl.add, StateT.run]

omit [Fintype F] [DecidableEq F] in
/-- Once set, the internal collision flag survives every later adaptive request. -/
theorem runBallotProofSim_flag_sticky {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (state : BallotProofOracleState F G)
    (hs : state.2 = true) (out : α × BallotProofOracleState F G)
    (ho : out ∈ support (runBallotProofSim g pk oa state)) : out.2.2 = true := by
  apply simulateQ_run_preservesInv (ballotProofSimImpl (F := F) g pk) (fun s => s.2 = true)
    ?_ oa state hs out ho
  intro t s hs' out' ho'
  cases t with
  | inl t =>
    simp only [ballotProofSimImpl, ballotProofImpl, QueryImpl.add, StateT.run,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho'
    obtain ⟨_,_,rfl⟩ := ho'
    exact hs'
  | inr wit =>
    simp only [ballotProofSimImpl, ballotProofImpl, QueryImpl.add, StateT.run,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ho'
    obtain ⟨_,_,rfl⟩ := ho'
    simp [hs']

#print axioms strongBallot_programming_distance_le
#print axioms runBallotProofReal_request
#print axioms runBallotProofSim_request
#print axioms runBallotProofSim_flag_sticky
#print axioms runBallotProofSim_cache_bound

end ExplainableCrypto.Helios.Computational
