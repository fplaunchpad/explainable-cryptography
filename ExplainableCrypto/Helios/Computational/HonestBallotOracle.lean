import ExplainableCrypto.Helios.Computational.BallotProgrammedOracle
import ExplainableCrypto.Helios.Computational.BallotProofProvenance

/-! Honest two-component ballots in the existing proof-request interface.
Nonces and proof coins retain the historical nonzero distributions. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def assembleHonestBallot (g pk : G) (vote : Bool) (rs : F × F)
    (p0 p1 pt : Proof01 F G) : Ballot F G 2 :=
  ⟨![encryptWith g pk rs.1 (voteScalar vote),encryptWith g pk rs.2 0],![p0,p1],pt⟩

def strongHonestBallotWithNoncesOracle (g pk : G) (vote : Bool) (rs : F × F) :
    OracleComp (BallotProofOracleSpec F G) (Ballot F G 2) := do
  let p0 ← ballotProofQuery (vote,rs.1)
  let p1 ← ballotProofQuery (false,rs.2)
  let pt ← ballotProofQuery (vote,rs.1+rs.2)
  pure (assembleHonestBallot g pk vote rs p0 p1 pt)

noncomputable def strongHonestBallotOracle [Fintype F] (g pk : G) (vote : Bool) :
    OracleComp (BallotProofOracleSpec F G) (Ballot F G 2) := do
  let rs ← liftComp (drawNoncePair F) _
  strongHonestBallotWithNoncesOracle g pk vote rs

/-- Original explicit coins, with only the hash interpreted as an oracle. -/
def strongHonestBallotWithCoinsOracle (g pk : G) (vote : Bool) (coins : HonestCoins F) :
    BallotOracleComp F G (Ballot F G 2) := do
  let p0 ← strongBallotProofWithCoinsOracle (honestProofStatement g pk (vote,coins.nonce 0))
    (vote,coins.nonce 0) (coins.witness 0,coins.challenge 0,coins.response 0)
  let p1 ← strongBallotProofWithCoinsOracle (honestProofStatement g pk (false,coins.nonce 1))
    (false,coins.nonce 1) (coins.witness 1,coins.challenge 1,coins.response 1)
  let pt ← strongBallotProofWithCoinsOracle
    (honestProofStatement g pk (vote,coins.nonce 0+coins.nonce 1))
    (vote,coins.nonce 0+coins.nonce 1) (coins.witness 2,coins.challenge 2,coins.response 2)
  pure (assembleHonestBallot g pk vote (coins.nonce 0,coins.nonce 1) p0 p1 pt)

theorem strongHonestBallotWithCoinsOracle_function (hash : StatementHash F G)
    (g pk : G) (vote : Bool) (coins : HonestCoins F) :
    simulateQ (ballotFunctionImpl hash) (strongHonestBallotWithCoinsOracle g pk vote coins) =
      pure (strongHonestBallot hash g pk vote coins) := by
  simp [strongHonestBallotWithCoinsOracle,simulateQ_bind,honestProofStatement,
    strongBallotProofWithCoinsOracle_function,assembleHonestBallot,strongHonestBallot]

noncomputable def ballotRealRequestImpl [Fintype F] (g pk : G) :
    QueryImpl (BallotProofOracleSpec F G) (BallotOracleComp F G) :=
  QueryImpl.add (spec₁ := BallotOracleSpec F G) (spec₂ := HonestBallotProofSpec F G)
    (fun t => liftM ((BallotOracleSpec F G).query t))
    (fun wit => strongBallotProofOracle (honestProofStatement g pk wit) wit)

variable [Fintype F] [SampleableType F] [DecidableEq G]

/-- Lowering actual honest requests preserves the whole lazy-oracle runtime.
The real-side sticky flag is unchanged, including initially true flags. -/
theorem ballotRealRequest_runtime_eq {α : Type} (g pk : G)
    (oa : OracleComp (BallotProofOracleSpec F G) α) (cache : BallotOracleCache F G) (bad : Bool) :
    runBallotProofReal g pk oa (cache,bad) =
      (fun out => (out.1,(out.2,bad))) <$>
        runBallotOracle (simulateQ (ballotRealRequestImpl g pk) oa) cache := by
  induction oa using OracleComp.inductionOn generalizing cache with
  | pure x => simp [runBallotProofReal,runBallotOracle]
  | query_bind t next ih =>
    simp only [runBallotProofReal,simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    cases t with
    | inl t =>
      simp only [ballotProofRealImpl,ballotProofImpl,QueryImpl.add,StateT.run]
      simp only [ballotRealRequestImpl,QueryImpl.add,runBallotOracle,simulateQ_bind,
        simulateQ_spec_query,StateT.run_bind,map_bind]
      simp only [bind_assoc,pure_bind]
      apply bind_congr
      intro out
      simpa [runBallotProofReal,ballotProofRealImpl,ballotProofImpl,QueryImpl.add,
        StateT.run,strongBallotRealOracle,runBallotOracle,ballotRealRequestImpl] using ih out.1 out.2
    | inr wit =>
      simp only [ballotProofRealImpl,ballotProofImpl,QueryImpl.add,StateT.run,
        strongBallotRealOracle,bind_map_left,Bool.or_false]
      simp only [ballotRealRequestImpl,QueryImpl.add,runBallotOracle,simulateQ_bind,
        StateT.run_bind,map_bind]
      simp only [bind_assoc,pure_bind]
      apply bind_congr
      intro out
      simpa [runBallotProofReal,ballotProofRealImpl,ballotProofImpl,QueryImpl.add,
        StateT.run,strongBallotRealOracle,runBallotOracle,ballotRealRequestImpl] using ih out.1 out.2

/-- The same historical coin record drawn nonce-first and proof-by-proof.
This auxiliary sampler is compared to the original, not assumed equivalent. -/
noncomputable def drawHonestCoinsByProof (F : Type) [Field F] [Fintype F] :
    ProbComp (HonestCoins F) := do
  let rs ← drawNoncePair F
  let t0 ← drawTriple F
  let t1 ← drawTriple F
  let tt ← drawTriple F
  pure ⟨![rs.1,rs.2],![t0 0,t1 0,tt 0],![t0 1,t1 1,tt 1],![t0 2,t1 2,tt 2]⟩

omit [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G] in
private theorem proofCoins_transpose {α : Type}
    (next : (Fin 3 → F) → (Fin 3 → F) → (Fin 3 → F) → ProbComp α) :
    𝒮[do let w ← drawTriple F; let e ← drawTriple F; let z ← drawTriple F; next w e z] =
    𝒮[do let t0 ← drawTriple F; let t1 ← drawTriple F; let tt ← drawTriple F
         next ![t0 0,t1 0,tt 0] ![t0 1,t1 1,tt 1] ![t0 2,t1 2,tt 2]] := by
  simp only [drawTriple,bind_assoc,pure_bind,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind]; arg 2; ext w2
    rw [evalSPMF_bind]; arg 2; ext e1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind]; arg 2; ext w2
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext z0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext z0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind]; arg 2; ext e1
    rw [evalSPMF_bind]; arg 2; ext w2
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext w0
    rw [evalSPMF_bind]; arg 2; ext e0
    rw [evalSPMF_bind]; arg 2; ext z0
    rw [evalSPMF_bind]; arg 2; ext w1
    rw [evalSPMF_bind]; arg 2; ext e1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  rfl

omit [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G] in
/-- Permuting independent nonzero draws preserves the complete historical coin
record distribution, including zero aggregate nonces arising from nonzero summands. -/
theorem drawHonestCoinsByProof_eq : 𝒮[drawHonestCoinsByProof F] = 𝒮[drawHonestCoins F] := by
  symm
  unfold drawHonestCoins drawHonestCoinsByProof
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext t0
    rw [evalSPMF_bind]; arg 2; ext t1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext t0
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr' (drawNoncePair F)
  intro rs
  exact proofCoins_transpose (F := F) (fun w e z => pure (⟨![rs.1,rs.2],w,e,z⟩ : HonestCoins F))

omit [Field F] [AddCommGroup G] [Module F G] [Fintype F] in
private theorem runBallotOracle_lift {α : Type} (oa : ProbComp α) (cache : BallotOracleCache F G) :
    runBallotOracle (liftComp oa (BallotOracleSpec F G)) cache =
      (fun x => (x,cache)) <$> oa := by
  have h := runBallotOracle_lift_bind (F := F) (G := G) oa
    (fun x => pure x) cache
  simpa only [bind_pure,runBallotOracle,simulateQ_pure,StateT.run_pure,bind_pure_comp] using h

omit [SampleableType F] [DecidableEq G] in
private theorem strongBallotProofOracle_triple (stmt : BallotStatement G) (wit : BallotWitness F) :
    strongBallotProofOracle stmt wit = (do
      let t ← liftComp (drawTriple F) (BallotOracleSpec F G)
      strongBallotProofWithCoinsOracle stmt wit (t 0,t 1,t 2)) := by
  simp [strongBallotProofOracle,drawTriple,liftComp_eq_liftM,monad_norm]

omit [SampleableType F] [DecidableEq G] in
private theorem honestRequests_lower (g pk : G) (vote : Bool) (rs : F × F) :
    simulateQ (ballotRealRequestImpl g pk) (strongHonestBallotWithNoncesOracle g pk vote rs) =
      (do
        let p0 ← strongBallotProofOracle (honestProofStatement g pk (vote,rs.1)) (vote,rs.1)
        let p1 ← strongBallotProofOracle (honestProofStatement g pk (false,rs.2)) (false,rs.2)
        let pt ← strongBallotProofOracle (honestProofStatement g pk (vote,rs.1+rs.2)) (vote,rs.1+rs.2)
        pure (assembleHonestBallot g pk vote rs p0 p1 pt)) := by
  simp only [strongHonestBallotWithNoncesOracle,ballotProofQuery,simulateQ_bind,
    simulateQ_spec_query,simulateQ_pure]
  rfl

/-- Nonce-fixed real requests may front-load their independent proof coins.
The final live cache is part of the distribution on both sides. -/
private theorem honestRequests_frontload (g pk : G) (vote : Bool) (rs : F × F)
    (cache : BallotOracleCache F G) :
    𝒮[runBallotOracle (simulateQ (ballotRealRequestImpl g pk)
      (strongHonestBallotWithNoncesOracle g pk vote rs)) cache] =
    𝒮[do
      let t0 ← drawTriple F
      let t1 ← drawTriple F
      let tt ← drawTriple F
      runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote
        ⟨![rs.1,rs.2],![t0 0,t1 0,tt 0],![t0 1,t1 1,tt 1],![t0 2,t1 2,tt 2]⟩) cache] := by
  rw [honestRequests_lower]
  simp only [strongBallotProofOracle_triple,bind_assoc]
  simp only [strongHonestBallotWithCoinsOracle,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  simp only [runBallotOracle_bind,runBallotOracle_lift,bind_map_left]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext t0
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext t0
    rw [evalSPMF_bind]; arg 2; ext t1
    rw [evalSPMF_bind]; arg 2; ext p0
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  conv_lhs =>
    rw [evalSPMF_bind]; arg 2; ext t0
    rw [evalSPMF_bind]; arg 2; ext t1
    rw [evalSPMF_bind_bind_swap]
  simp only [← evalSPMF_bind]
  rfl

omit [SampleableType F] [DecidableEq G] in
private theorem ballotRealRequest_lift {α : Type} (g pk : G) (oa : ProbComp α) :
    simulateQ (ballotRealRequestImpl g pk) (liftComp oa (BallotProofOracleSpec F G)) =
      liftComp oa (BallotOracleSpec F G) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    rw [liftComp_bind,simulateQ_bind,liftComp_bind]
    have hq : simulateQ (ballotRealRequestImpl (F := F) g pk)
        (liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotProofOracleSpec F G)) =
        liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotOracleSpec F G) := by
      change simulateQ (ballotRealRequestImpl (F := F) g pk)
        (liftM ((BallotProofOracleSpec F G).query (.inl (.inl t)))) =
        liftM ((BallotOracleSpec F G).query (.inl t))
      rw [simulateQ_spec_query]
      rfl
    rw [hq]
    exact bind_congr ih

private theorem strongHonestBallotOracle_raw_real_eq (g pk : G) (vote : Bool)
    (cache : BallotOracleCache F G) :
    𝒮[runBallotOracle (simulateQ (ballotRealRequestImpl g pk)
      (strongHonestBallotOracle g pk vote)) cache] =
    𝒮[do let coins ← drawHonestCoins F
         runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote coins) cache] := by
  conv_rhs => rw [evalSPMF_bind,← drawHonestCoinsByProof_eq,← evalSPMF_bind]
  simp only [strongHonestBallotOracle,simulateQ_bind,ballotRealRequest_lift,
    runBallotOracle_lift_bind,drawHonestCoinsByProof,bind_assoc,pure_bind]
  exact evalSPMF_bind_congr' (drawNoncePair F) (fun rs => honestRequests_frontload g pk vote rs cache)

/-- Actual request execution has the distribution of the historical coin
sampler and explicit-coin ballot algorithm, including final cache and flag. -/
theorem strongHonestBallotOracle_real_eq (g pk : G) (vote : Bool)
    (cache : BallotOracleCache F G) (bad : Bool) :
    𝒮[runBallotProofReal g pk (strongHonestBallotOracle g pk vote) (cache,bad)] =
    𝒮[do let coins ← drawHonestCoins F
         let out ← runBallotOracle (strongHonestBallotWithCoinsOracle g pk vote coins) cache
         pure (out.1,(out.2,bad))] := by
  rw [ballotRealRequest_runtime_eq]
  have h := strongHonestBallotOracle_raw_real_eq g pk vote cache
  simpa only [← evalSPMF_map,map_bind,bind_pure_comp] using
    congrArg (fun d => (fun out => (out.1,(out.2,bad))) <$> d) h

omit [Fintype F] in
/-- Actual simulated requests record exactly the two returned component
statements and their implicit aggregate, in reverse request order. -/
theorem strongHonestBallotWithNoncesOracle_request_targets (g pk : G) (vote : Bool) (rs : F × F)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (strongHonestBallotWithNoncesOracle g pk vote rs)).run state) live)) :
    out.1.2.programmed = [out.1.1.coveredStatement g pk none,
      out.1.1.coveredStatement g pk (some 1),out.1.1.coveredStatement g pk (some 0)] ++ state.programmed := by
  simp only [strongHonestBallotWithNoncesOracle,ballotProofQuery,
    simulateQ_bind,simulateQ_spec_query,simulateQ_pure,StateT.run_bind,StateT.run_pure] at ho
  simp only [ballotProgrammedImpl,ballotProgrammedStatement,QueryImpl.add,StateT.run,bind_assoc,pure_bind] at ho
  simp only [runBallotOracle_lift_bind] at ho
  simp only [runBallotOracle,simulateQ_pure,StateT.run_pure,support_bind,support_pure,
    Set.mem_iUnion,Set.mem_singleton_iff] at ho
  obtain ⟨a,ha,b,hb,c,hc,rfl⟩ := ho
  simp [assembleHonestBallot,Ballot.coveredStatement,
    Ballot.coveredCiphertext,Ballot.aggregate,Fin.sum_univ_two,encryptWith_add,
    honestProofStatement,voteScalar]

omit [Fintype F] in
private theorem ballotProgrammed_lift {α : Type} (g pk : G) (oa : ProbComp α)
    (state : BallotProgrammedState F G) :
    (simulateQ (ballotProgrammedImpl g pk) (liftComp oa (BallotProofOracleSpec F G))).run state =
      (fun x => (x,state)) <$> liftComp oa (BallotOracleSpec F G) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    rw [liftComp_bind,simulateQ_bind,StateT.run_bind]
    have hq : (simulateQ (ballotProgrammedImpl (F := F) g pk)
        (liftComp (liftM (unifSpec.query t) : ProbComp _) (BallotProofOracleSpec F G))).run state =
        (fun x => (x,state)) <$> liftM ((BallotOracleSpec F G).query (.inl t)) := by
      change (simulateQ (ballotProgrammedImpl (F := F) g pk)
        (liftM ((BallotProofOracleSpec F G).query (.inl (.inl t))))).run state = _
      rw [simulateQ_spec_query]
      rfl
    rw [hq]
    simp only [bind_map_left,liftComp_bind,map_bind]
    apply bind_congr
    exact ih

private theorem strongHonestBallotOracle_programmed_run (g pk : G) (vote : Bool)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G) :
    runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (strongHonestBallotOracle (F := F) g pk vote)).run state) live =
      (do let rs ← drawNoncePair F
          runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
            (strongHonestBallotWithNoncesOracle g pk vote rs)).run state) live) := by
  simp only [strongHonestBallotOracle,simulateQ_bind,StateT.run_bind,
    ballotProgrammed_lift,bind_map_left]
  rw [runBallotOracle_lift_bind]

/-- The sampled program prepends exactly the covered statements of the ballot
it actually returns. This composes with prior requests and cached answers. -/
theorem strongHonestBallotOracle_request_targets (g pk : G) (vote : Bool)
    (state : BallotProgrammedState F G) (live : BallotOracleCache F G)
    (out : (Ballot F G 2 × BallotProgrammedState F G) × BallotOracleCache F G)
    (ho : out ∈ support (runBallotOracle ((simulateQ (ballotProgrammedImpl g pk)
      (strongHonestBallotOracle g pk vote)).run state) live)) :
    out.1.2.programmed = [out.1.1.coveredStatement g pk none,
      out.1.1.coveredStatement g pk (some 1),out.1.1.coveredStatement g pk (some 0)] ++ state.programmed := by
  simp only [strongHonestBallotOracle_programmed_run,support_bind,Set.mem_iUnion] at ho
  obtain ⟨rs,hrs,ho⟩ := ho
  exact strongHonestBallotWithNoncesOracle_request_targets g pk vote rs state live out ho

omit [Field F] [AddCommGroup G] [Module F G] [Fintype F] [SampleableType F] [DecidableEq G] in
theorem honestUniform_query_bound {α : Type} (oa : ProbComp α)
    (pred : (BallotProofOracleSpec F G).Domain → Prop) [DecidablePred pred]
    (hp : ∀ n, ¬ pred (.inl (.inl n))) :
    (liftComp oa (BallotProofOracleSpec F G)).IsQueryBoundP pred 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t next ih =>
    rw [liftComp_bind]
    change (do let u ← liftM ((BallotProofOracleSpec F G).query (.inl (.inl t)))
               liftComp (next u) (BallotProofOracleSpec F G)).IsQueryBoundP pred 0
    simp [isQueryBoundP_query_bind_iff,hp,ih]

omit [SampleableType F] [DecidableEq G] in
/-- The actual sampled ballot makes three honest proof requests; independent
nonce sampling consumes none of the hash-or-proof query budget. -/
theorem strongHonestBallotOracle_query_bounds (g pk : G) (vote : Bool) :
    (strongHonestBallotOracle (F := F) g pk vote).IsQueryBoundP growsBallotCache 3 ∧
    (strongHonestBallotOracle (F := F) g pk vote).IsQueryBoundP isBallotProofRequest 3 := by
  unfold strongHonestBallotOracle
  constructor
  · exact isQueryBoundP_bind (n := 0) (m := 3)
      (honestUniform_query_bound (F := F) (G := G) (drawNoncePair F) growsBallotCache (by simp [growsBallotCache]))
      (fun rs _ => by simp [strongHonestBallotWithNoncesOracle,ballotProofQuery,growsBallotCache])
  · exact isQueryBoundP_bind (n := 0) (m := 3)
      (honestUniform_query_bound (F := F) (G := G) (drawNoncePair F) isBallotProofRequest (by simp [isBallotProofRequest]))
      (fun rs _ => by simp [strongHonestBallotWithNoncesOracle,ballotProofQuery,isBallotProofRequest])

/-- State-inclusive simulation bound for the actual honest ballot program.
Board decisions and trustee observations still have to be composed with it. -/
theorem strongHonestBallotOracle_simulation_le [DecidableEq F] (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (vote : Bool)
    (state : BallotProofOracleState F G) (k : Nat) (hk : BallotCacheBound state.1 k) :
    tvDist (runBallotProofReal g pk (strongHonestBallotOracle g pk vote) state)
      (runBallotProofSim g pk (strongHonestBallotOracle g pk vote) state) ≤
        3 * (6 + (k : ℝ)) / (Fintype.card F : ℝ) := by
  have hb := strongHonestBallotOracle_query_bounds (F := F) g pk vote
  have h := strongBallot_programming_distance_le g pk hg (strongHonestBallotOracle g pk vote)
    3 3 k hb.1 hb.2 state hk
  convert h using 1
  push_cast
  ring

#print axioms honestUniform_query_bound
#print axioms strongHonestBallotWithCoinsOracle_function
#print axioms ballotRealRequest_runtime_eq
#print axioms drawHonestCoinsByProof_eq
#print axioms strongHonestBallotOracle_real_eq
#print axioms strongHonestBallotWithNoncesOracle_request_targets
#print axioms strongHonestBallotOracle_request_targets
#print axioms strongHonestBallotOracle_query_bounds
#print axioms strongHonestBallotOracle_simulation_le
end ExplainableCrypto.Helios.Computational
