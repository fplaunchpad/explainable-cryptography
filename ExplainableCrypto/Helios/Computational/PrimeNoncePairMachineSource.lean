import ExplainableCrypto.Helios.Computational.PrimeNoncePairMachineRun

/-! Joint source correspondence and derived physical cost for the actual two-call
nonce controller. The saved context remains an explicit private machine word. -/
namespace ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem nonce_word_source {q : Nat} [Fact q.Prime] (slack : Nat) :
    (fun bits => uniformNatEncode (bitsValue bits % (q-1)+1)) <$>
      CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q) =
      simulateQ CoinWordLoader.liftCoins
        (scalarEncode <$> runFairBitUniform slack (samplePrimeNonzero (q := q))) := by
  obtain ⟨c,_,he⟩ := PrimeNonceMachine.sample_source slack q (Fact.out : q.Prime).two_le (fun _ => [])
  have h := congrArg (fun oa => (fun cfg : Config 11 71 3 => cfg.stk 5) <$> oa)
    (PrimeNonceMachine.sample_execution_source (q := q) slack (fun _ => []))
  rw [he] at h
  have hout (word modulus : List Bool) (frame : PrimeNonceMachine.Frame) :
      (PrimeNonceMachine.sampleOutput word modulus frame).stk 5 = word := rfl
  simpa only [Functor.map_map,simulateQ_map,Function.comp_def,hout] using h

/-- Exact joint historical source tree: the second sampler uses successive
fresh coin queries, and both results are retained in their caller slots. -/
theorem pair_execution_source {q : Nat} [Fact q.Prime] (slack : Nat) (context : List Bool) :
    Prod.fst <$> run code (clock slack q) (start (SamplerOperands.input slack q []) context) =
      simulateQ CoinWordLoader.liftCoins
        ((fun rs : ZMod q × ZMod q => result (SamplerOperands.input slack q [])
          (scalarEncode rs.1) (scalarEncode rs.2) (q-1).bits context) <$>
          runFairBitUniform slack (drawPrimeNoncePair (q := q))) := by
  obtain ⟨c,_,he⟩ := pair_run slack q (Fact.out : q.Prime).two_le context
  rw [he]
  let W := (fun bits => uniformNatEncode (bitsValue bits % (q-1)+1)) <$>
    CoinWordLoader.word (PrimeNonceMachine.sampleWidth slack q)
  have hW := nonce_word_source (q := q) slack
  change W = _ at hW
  calc
    _ = (do
      let a ← W
      let b ← W
      pure (result (SamplerOperands.input slack q []) a b (q-1).bits context)) := by
      simp only [W,map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
    _ = _ := by
      rw [hW]
      simp only [drawPrimeNoncePair,runFairBitUniform,simulateQ_bind,simulateQ_pure,
        map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

private def samplingCoins : QueryImpl spec (OracleComp coinSpec) := fun r =>
  match r with
  | .coin => coin
  | .hash word => pure word

private theorem samplingCoins_lift {A : Type} (oa : OracleComp coinSpec A) :
    simulateQ samplingCoins (simulateQ CoinWordLoader.liftCoins oa) = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    cases t
    simp [simulateQ_bind,CoinWordLoader.liftCoins,ih]
    rfl

/-- Actual pair execution with fair coins; the source theorem excludes hash queries. -/
def pairExperiment (slack q : Nat) (context : List Bool) : OracleComp coinSpec (Config 11 size 3) :=
  simulateQ samplingCoins (Prod.fst <$> run code (clock slack q)
    (start (SamplerOperands.input slack q []) context))

/-- Preserve the complete joint result law, including record and saved context. -/
theorem pair_experiment_source {q : Nat} [Fact q.Prime] (slack : Nat) (context : List Bool) :
    pairExperiment slack q context =
      (fun rs : ZMod q × ZMod q => result (SamplerOperands.input slack q [])
        (scalarEncode rs.1) (scalarEncode rs.2) (q-1).bits context) <$>
        runFairBitUniform slack (drawPrimeNoncePair (q := q)) := by
  rw [pairExperiment,pair_execution_source,samplingCoins_lift]

private theorem pair_query_bound {q : Nat} [Fact q.Prime] :
    (drawPrimeNoncePair (q := q)).IsTotalQueryBound 2 := by
  unfold drawPrimeNoncePair
  apply isTotalQueryBound_bind (n₁ := 1) (n₂ := 1) samplePrimeNonzero_total_bound
  intro r
  exact isTotalQueryBound_bind (n₁ := 1) (n₂ := 0) samplePrimeNonzero_total_bound (fun _ => trivial)

/-- The executed pair retains the two-draw statistical bound against the exact
historical nonce pair, rather than only proving either marginal or equal tallies. -/
theorem pair_loss {q : Nat} [Fact q.Prime] (slack : Nat) (context : List Bool) :
    SPMF.tvDist (evalSPMF (pairExperiment slack q context))
      (evalSPMF ((fun rs : ZMod q × ZMod q => result (SamplerOperands.input slack q [])
        (scalarEncode rs.1) (scalarEncode rs.2) (q-1).bits context) <$>
        drawPrimeNoncePair (q := q))) ≤ 2*((2 : ℝ)^slack)⁻¹ := by
  rw [pair_experiment_source,evalSPMF_map,evalSPMF_map]
  refine (SPMF.tvDist_map_le _ _ _).trans ?_
  exact runFairBitUniform_tv_le slack (drawPrimeNoncePair (q := q)) 2 pair_query_bound

private theorem within_support (limit bound : Nat)
    (oa : OracleComp spec (Config 11 size 3 × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

/-- The actual pair's full branchwise halt and charge discharge the primitive
compiler contract, including all record reload and first-answer storage work. -/
theorem pair_within (slack q limit : Nat) (hq : 2 ≤ q) (context : List Bool) :
    BitOracleLoopBounded.Within limit (cost slack q)
      (run code (clock slack q) (start (SamplerOperands.input slack q []) context)) := by
  obtain ⟨c,hc,he⟩ := pair_run slack q hq context
  apply within_support
  rw [he]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨a,ha,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨b,hb,ho⟩ := ho
  have hv := eq_of_mem_support_pure _ ho
  subst out
  exact ⟨rfl,hc a (CoinWordLoader.word_length _ _ ha) b (CoinWordLoader.word_length _ _ hb)⟩

/-- Derived physical execution from the resident public record and saved private
context. Actual initial height is charged; no polynomial context certificate or
assumed correspondence is supplied by the caller. -/
theorem pair_physical_run {q : Nat} [Fact q.Prime] (slack limit : Nat) (context : List Bool) :
    let cfg := start (SamplerOperands.input slack q []) context
    let B := cost slack q
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor code
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run code T
        (BitOraclePrimitiveLoop.lower code (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      (some ∘ fun rs : ZMod q × ZMod q => result (SamplerOperands.input slack q [])
        (scalarEncode rs.1) (scalarEncode rs.2) (q-1).bits context) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (drawPrimeNoncePair (q := q)))) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded code (clock slack q) limit (cost slack q)
    (start (SamplerOperands.input slack q []) context) [] (OracleTapeOutput.wordTape [])
    (pair_within slack q limit (Fact.out : q.Prime).two_le context)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (pair_execution_source (q := q) slack context)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms pair_execution_source
#print axioms pair_experiment_source
#print axioms pair_loss
#print axioms pair_within
#print axioms pair_physical_run
end ExplainableCrypto.Helios.Computational.PrimeNoncePairMachine
