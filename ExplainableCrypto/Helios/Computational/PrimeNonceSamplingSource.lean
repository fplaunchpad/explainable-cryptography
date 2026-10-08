import ExplainableCrypto.Helios.Computational.PrimeNonceSampling
import ExplainableCrypto.Helios.Computational.NonceOperandsRun
import ExplainableCrypto.Helios.Computational.BitOraclePrimitiveBounded

namespace ExplainableCrypto.Helios.Computational.PrimeNonceMachine
open OracleComp OracleSpec BitOracleMachine
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind

private theorem operand_code (l : Fin NonceOperands.size) : sampleCode (operandLabel l) =
    BitOracleReturnLink.command operandLabel (some 15) (operandCode l) := by
  fin_cases l <;> rfl
private theorem tail_code (l : Fin 55) : sampleCode (tailLabel l) =
    BitOracleReturnLink.command tailLabel none (sampleTailCode l) := by
  have ha : ¬ (tailLabel l).val < 15 := by simp only [tailLabel]; omega
  have hb : tailLabel l ≠ 15 := by
    intro h
    have he := congrArg Fin.val h
    change l.val+16 = 15 at he
    omega
  rw [sampleCode,dif_neg ha,if_neg hb]
  rfl

private theorem tail_run (fuel : Nat) (cfg : BitOracleMachine.Config 11 55 3) :
    run sampleCode fuel (BitOracleReturnLink.embed tailLabel none cfg) =
      (fun out => (BitOracleReturnLink.embed tailLabel none out.1,out.2)) <$>
        run sampleTailCode fuel cfg :=
  BitOracleReturnLink.rename_run sampleTailCode sampleCode tailLabel tail_code fuel cfg

private theorem operand_gate (slack q : Nat) (frame : Frame) :
    step sampleCode (BitOracleReturnLink.embed operandLabel (some 15)
      (BitOracleStackFrame.embed sampleLayout (NonceOperands.result slack q [] (fun _ => [])) frame)) =
      pure (BitOracleReturnLink.embed tailLabel none
        (sampleTailStart (List.replicate (sampleWidth slack q) true) (q-1) frame),5) := by
  apply congrArg pure
  change ((⟨some (tailLabel (coinLabel 15)),0,_⟩ : BitOracleMachine.Config 11 71 3),5) =
    ((⟨some (tailLabel (coinLabel 15)),0,_⟩ : BitOracleMachine.Config 11 71 3),5)
  congr 2

private theorem after_operand (slack q : Nat) (hq : 2 ≤ q) (frame : Frame) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = sampleWidth slack q → charge bits ≤ 5+tailCost (sampleWidth slack q) (q-1)) ∧
      run sampleCode (1+tailClock (sampleWidth slack q) (q-1))
        (BitOracleReturnLink.embed operandLabel (some 15)
          (BitOracleStackFrame.embed sampleLayout (NonceOperands.result slack q [] (fun _ => [])) frame)) =
        (fun bits => (sampleOutput (uniformNatEncode (bitsValue bits % (q-1)+1)) (q-1).bits frame,
          charge bits)) <$> CoinWordLoader.word (sampleWidth slack q) := by
  obtain ⟨c,hc,he⟩ := tail_source (List.replicate (sampleWidth slack q) true) (q-1) (by omega) frame
  simp only [List.length_replicate] at hc he
  refine ⟨fun bits => 5+c bits,?_,?_⟩
  · intro bits hb
    exact Nat.add_le_add_left (hc bits hb) 5
  · rw [Nat.add_comm 1,run,operand_gate,pure_bind,tail_run,he]
    simp [Functor.map_map,sampleOutput]

/-- From original serialized q/slack and explicit saved data, one fixed program
executes predecessor/width preparation, coins, division and the nonce successor.
The full query tree, complete result, halt and combined charge are derived. -/
theorem sample_source (slack q : Nat) (hq : 2 ≤ q) (frame : Frame) :
    ∃ charge : List Bool → Nat,
      (∀ bits, bits.length = sampleWidth slack q → charge bits ≤ sampleCost slack q) ∧
      run sampleCode (sampleClock slack q) (sampleStart (SamplerOperands.input slack q []) frame) =
        (fun bits => (sampleOutput (uniformNatEncode (bitsValue bits % (q-1)+1)) (q-1).bits frame,
          charge bits)) <$> CoinWordLoader.word (sampleWidth slack q) := by
  obtain ⟨c,hc,he⟩ := NonceOperands.charged slack q hq
  have hfr : run operandCode (NonceOperands.clock slack q)
      (BitOracleStackFrame.embed sampleLayout (NonceOperands.startWord (SamplerOperands.input slack q [])) frame) =
      pure (BitOracleStackFrame.embed sampleLayout (NonceOperands.result slack q [] (fun _ => [])) frame,c) := by
    rw [operandCode,BitOracleStackFrame.run,he,map_pure]
  obtain ⟨tail,ht,htRun⟩ := after_operand slack q hq frame
  have hh : ∀ out ∈ support (run operandCode (NonceOperands.clock slack q)
      (BitOracleStackFrame.embed sampleLayout (NonceOperands.startWord (SamplerOperands.input slack q [])) frame)),
      out.1.l = none := by
    intro out ho
    rw [hfr] at ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    rfl
  have hhalt : ∀ out ∈ support (run operandCode (NonceOperands.clock slack q)
      (BitOracleStackFrame.embed sampleLayout (NonceOperands.startWord (SamplerOperands.input slack q [])) frame)),
      ∀ last ∈ support (run sampleCode (1+tailClock (sampleWidth slack q) (q-1))
        (BitOracleReturnLink.embed operandLabel (some 15) out.1)), last.1.l = none := by
    intro out ho
    rw [hfr] at ho
    have hv := eq_of_mem_support_pure _ ho
    subst out
    intro last hl
    rw [htRun] at hl
    obtain ⟨bits,_,rfl⟩ := mem_support_map_peel _ _ hl
    rfl
  have hr := BitOracleReturnLink.run operandCode sampleCode operandLabel 15 operand_code
    (NonceOperands.clock slack q) (1+tailClock (sampleWidth slack q) (q-1))
    (BitOracleStackFrame.embed sampleLayout (NonceOperands.startWord (SamplerOperands.input slack q [])) frame)
    hh hhalt
  refine ⟨fun bits => c+tail bits,?_,?_⟩
  · intro bits hb
    have h := ht bits hb
    change c+tail bits ≤ NonceOperands.cost slack q+5+tailCost (sampleWidth slack q) (q-1)
    omega
  · rw [sampleClock,Nat.add_assoc,sampleStart,hr,hfr,pure_bind,htRun]
    simp [Functor.map_map]

private theorem uniform_eq (m slack : Nat) [NeZero m] :
    runFairBitUniform slack (uniformSample (Fin m)) = sampleFairBitRange m slack := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m =>
    change simulateQ (fairBitUniformImpl slack) (liftM (unifSpec.query m)) = _
    simp [fairBitUniformImpl]

private theorem nonce_fair_syntax {q : Nat} [Fact q.Prime] (slack : Nat) :
    letI : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
    runFairBitUniform slack (samplePrimeNonzero (q := q)) =
      primeNonceValue <$> sampleFairBitRange (q-1) slack := by
  have : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  unfold samplePrimeNonzero runFairBitUniform
  rw [simulateQ_map]
  change primeNonceValue <$> runFairBitUniform slack (uniformSample (Fin (q-1))) = _
  rw [uniform_eq]

/-- Exact full-state query-tree correspondence to the existing historical
nonce source after its already specified fair-bit transformation. -/
theorem sample_execution_source {q : Nat} [Fact q.Prime] (slack : Nat) (frame : Frame) :
    Prod.fst <$> run sampleCode (sampleClock slack q)
      (sampleStart (SamplerOperands.input slack q []) frame) =
      simulateQ CoinWordLoader.liftCoins
        ((fun a => sampleOutput (scalarEncode a) (q-1).bits frame) <$>
          runFairBitUniform slack (samplePrimeNonzero (q := q))) := by
  have : NeZero (q-1) := ⟨by have := (Fact.out : q.Prime).two_le; omega⟩
  obtain ⟨c,_,he⟩ := sample_source slack q (Fact.out : q.Prime).two_le frame
  rw [he,nonce_fair_syntax]
  simp only [Functor.map_map]
  have hencode (i : Fin (q-1)) : scalarEncode (primeNonceValue i) = uniformNatEncode (i.val+1) := by
    have hi : i.val+1 < q := by have := i.isLt; omega
    simp only [scalarEncode,primeNonceValue,ZMod.val_natCast_of_lt hi]
  have h := congrArg (fun oa : OracleComp spec Nat =>
    (fun n => sampleOutput (uniformNatEncode (n % (q-1)+1)) (q-1).bits frame) <$> oa)
    (CoinWordLoader.word_index (sampleWidth slack q))
  simpa only [simulateQ_map,Functor.map_map,Function.comp_def,sampleFairBitRange,
    sampleFairBitModulo,hencode,sampleWidth] using h

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

/-- Run the actual machine with fair coins. No hash request is reachable, as
sample_execution_source proves; the unused handler branch is immaterial. -/
def sampleExperiment (slack q : Nat) (frame : Frame) : OracleComp coinSpec (BitOracleMachine.Config 11 71 3) :=
  simulateQ samplingCoins (Prod.fst <$> run sampleCode (sampleClock slack q)
    (sampleStart (SamplerOperands.input slack q []) frame))

/-- Complete result law of actual execution, including retained modulus/frame. -/
theorem sample_experiment_source {q : Nat} [Fact q.Prime] (slack : Nat) (frame : Frame) :
    sampleExperiment slack q frame =
      (fun a => sampleOutput (scalarEncode a) (q-1).bits frame) <$>
        runFairBitUniform slack (samplePrimeNonzero (q := q)) := by
  rw [sampleExperiment,sample_execution_source,samplingCoins_lift]

/-- The actual complete sampler result retains the original one-draw error
bound relative to exact historical nonzero sampling. This is not exact uniformity. -/
theorem sample_loss {q : Nat} [Fact q.Prime] (slack : Nat) (frame : Frame) :
    SPMF.tvDist (evalSPMF (sampleExperiment slack q frame))
      (evalSPMF ((fun a => sampleOutput (scalarEncode a) (q-1).bits frame) <$>
        samplePrimeNonzero (q := q))) ≤ ((2 : ℝ)^slack)⁻¹ := by
  rw [sample_experiment_source,evalSPMF_map,evalSPMF_map]
  refine (SPMF.tvDist_map_le _ _ _).trans ?_
  simpa only [Nat.cast_one,one_mul] using
    runFairBitUniform_tv_le slack (samplePrimeNonzero (q := q)) 1 samplePrimeNonzero_total_bound

private theorem sample_word_within (limit bound w : Nat)
    (f : List Bool → BitOracleMachine.Config 11 71 3 × Nat)
    (hf : ∀ bits, bits.length = w → (f bits).1.l = none ∧ (f bits).2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound (f <$> CoinWordLoader.word w) := by
  induction w generalizing f with
  | zero => exact hf [] rfl
  | succ w ih =>
    simp only [CoinWordLoader.word,map_bind,map_pure]
    change ∀ b : Bool, True → BitOracleLoopBounded.Within limit bound
      (CoinWordLoader.word w >>= fun bits => pure (f (b::bits)))
    intro b _
    simpa only [map_eq_bind_pure_comp,Function.comp_def] using
      ih (fun bits => f (b::bits)) (fun bits hb => hf (b::bits) (by simp [hb]))

/-- Actual halt and charge on every coin branch discharge the existing
primitive compiler contract for the complete nonce sampler. -/
theorem sample_within (slack q limit : Nat) (hq : 2 ≤ q) (frame : Frame) :
    BitOracleLoopBounded.Within limit (sampleCost slack q)
      (run sampleCode (sampleClock slack q) (sampleStart (SamplerOperands.input slack q []) frame)) := by
  obtain ⟨c,hc,he⟩ := sample_source slack q hq frame
  rw [he]
  apply sample_word_within
  intro bits hb
  exact ⟨rfl,hc bits hb⟩

/-- The existing primitive compiler executes the complete historical nonce
sampler from its resident input/frame. The full saved-data height is charged;
no polynomial-width or missing runtime certificate is assumed. -/
theorem sample_physical_run {q : Nat} [Fact q.Prime] (slack limit : Nat) (frame : Frame) :
    let cfg := sampleStart (SamplerOperands.input slack q []) frame
    let B := sampleCost slack q
    let T := BitOracleTapeCap.unitCost (TM2TapeRuns.height cfg.stk+B)*B*
      BitOraclePrimitiveLoop.globalFactor sampleCode
    BitOraclePrimitiveBounded.observe <$> simulateQ (BitOracleLoopBounded.adapter limit)
      (BitOraclePrimitiveLoop.run sampleCode T
        (BitOraclePrimitiveLoop.lower sampleCode (BitOracleTapeLoop.ready cfg
          (OracleTapeOutput.wordTape []) (OracleTapeOutput.wordTape [])))) =
      (some ∘ fun a => sampleOutput (scalarEncode a) (q-1).bits frame) <$>
        simulateQ (BitOracleLoopBounded.adapter limit)
          (simulateQ CoinWordLoader.liftCoins (runFairBitUniform slack (samplePrimeNonzero (q := q)))) := by
  dsimp only
  have h := BitOraclePrimitiveBounded.run_source_bounded sampleCode (sampleClock slack q) limit
    (sampleCost slack q) (sampleStart (SamplerOperands.input slack q []) frame)
    [] (OracleTapeOutput.wordTape []) (sample_within slack q limit (Fact.out : q.Prime).two_le frame)
  simp only [List.length_nil,Nat.add_zero] at h
  rw [h]
  have hr := congrArg (fun oa => simulateQ (BitOracleLoopBounded.adapter limit) oa)
    (sample_execution_source (q := q) slack frame)
  simp only [simulateQ_map] at hr
  have lifted := congrArg (fun oa => some <$> oa) hr
  simpa only [Functor.map_map,Function.comp_def] using lifted

#print axioms sample_source
#print axioms sample_execution_source
#print axioms sample_experiment_source
#print axioms sample_loss
#print axioms sample_within
#print axioms sample_physical_run
end ExplainableCrypto.Helios.Computational.PrimeNonceMachine
