import ExplainableCrypto.Helios.Computational.FairBitSampler
import VCVio.OracleComp.Coercions.SubSpec

/-! Replace actual adaptive uniform-range requests with fixed-width fair-bit
sampling. Statistical loss composes over the original program's query budget. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

/-- Preserve each requested response type Fin(t+1), with width chosen from t+1. -/
def fairBitUniformImpl (slack : Nat) : QueryImpl unifSpec (OracleComp coinSpec) :=
  fun t => sampleFairBitRange (t+1) slack

def runFairBitUniform {A : Type} (slack : Nat) (oa : ProbComp A) : OracleComp coinSpec A :=
  simulateQ (fairBitUniformImpl slack) oa

private theorem uniform_query_eq (t : Nat) :
    evalSPMF (liftM (unifSpec.query t) : ProbComp (Fin (t+1))) =
      evalSPMF (uniformSample (Fin (t+1))) := by
  apply evalSPMF_ext
  intro x
  simp

private theorem mixed_bind_tv_le {A B : Type} (oa : ProbComp B)
    (f : B → OracleComp coinSpec A) (g : B → ProbComp A) (c : ℝ)
    (hfg : ∀ x, SPMF.tvDist (evalSPMF (f x)) (evalSPMF (g x)) ≤ c) :
    SPMF.tvDist (evalSPMF oa >>= fun x => evalSPMF (f x))
      (evalSPMF oa >>= fun x => evalSPMF (g x)) ≤ c := by
  have h := tvDist_bind_left_le_const' (liftComp oa (unifSpec + coinSpec))
    (fun x => liftComp (f x) (unifSpec + coinSpec))
    (fun x => liftComp (g x) (unifSpec + coinSpec)) c
    (by intro x; simpa only [tvDist,evalSPMF_liftComp] using hfg x)
  simpa only [tvDist,evalSPMF_bind,evalSPMF_liftComp] using h

/-- The sampler error accumulates along the actual adaptive computation.
No range-size bound or source-correspondence assumption is supplied by callers. -/
theorem runFairBitUniform_tv_le {A : Type} (slack : Nat) (oa : ProbComp A)
    (n : Nat) (hb : oa.IsTotalQueryBound n) :
    SPMF.tvDist (evalSPMF (runFairBitUniform slack oa)) (evalSPMF oa) ≤
      (n : ℝ) * ((2 : ℝ)^slack)⁻¹ := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp [runFairBitUniform]
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hb
    cases n with
    | zero => omega
    | succ n =>
      have hn (x : Fin (t+1)) := ih x n (by simpa using hb.2 x)
      have hstep := sampleFairBitRange_tv_le (t+1) slack
      rw [← uniform_query_eq t] at hstep
      have hc := SPMF.tvDist_bind_right_le
        (fun x => evalSPMF (runFairBitUniform slack (next x)))
        (evalSPMF (sampleFairBitRange (t+1) slack))
        (evalSPMF (liftM (unifSpec.query t) : ProbComp (Fin (t+1))))
      have hr := mixed_bind_tv_le (liftM (unifSpec.query t) : ProbComp (Fin (t+1)))
        (fun x => runFairBitUniform slack (next x)) next
        ((n : ℝ)*((2 : ℝ)^slack)⁻¹) hn
      have ht := SPMF.tvDist_triangle
        (evalSPMF (sampleFairBitRange (t+1) slack) >>= fun x =>
          evalSPMF (runFairBitUniform slack (next x)))
        (evalSPMF (liftM (unifSpec.query t) : ProbComp (Fin (t+1))) >>= fun x =>
          evalSPMF (runFairBitUniform slack (next x)))
        (evalSPMF (liftM (unifSpec.query t) : ProbComp (Fin (t+1))) >>= fun x =>
          evalSPMF (next x))
      have h := ht.trans (add_le_add (hc.trans hstep) hr)
      have he : runFairBitUniform slack (liftM (unifSpec.query t) >>= next) =
          sampleFairBitRange (t+1) slack >>= fun x => runFairBitUniform slack (next x) := by
        simp [runFairBitUniform,fairBitUniformImpl]
      rw [he,evalSPMF_bind,evalSPMF_bind]
      exact h.trans_eq (by rw [Nat.cast_succ]; ring)

/-- Finite-range answers preserve reachable outputs even though their masses
change. This derives witness-validity transport independently of the TV bound. -/
theorem runFairBitUniform_support_subset {A : Type} (slack : Nat) (oa : ProbComp A) :
    support (runFairBitUniform slack oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [runFairBitUniform]
  | query_bind t next ih =>
    intro x hx
    have he : runFairBitUniform slack (liftM (unifSpec.query t) >>= next) =
        sampleFairBitRange (t+1) slack >>= fun y => runFairBitUniform slack (next y) := by
      simp [runFairBitUniform,fairBitUniformImpl]
    rw [he] at hx
    simp only [support_bind,Set.mem_iUnion,exists_prop] at hx ⊢
    obtain ⟨y,_,hy⟩ := hx
    exact ⟨y,by simp,ih y hy⟩

/-- Any Boolean observation of the complete result has the same accumulated
sampling-error bound. -/
theorem runFairBitUniform_event_error {A : Type} (slack : Nat) (oa : ProbComp A)
    (n : Nat) (hb : oa.IsTotalQueryBound n) (P : A → Bool) :
    |Pr[fun x => P x | runFairBitUniform slack oa].toReal - Pr[fun x => P x | oa].toReal| ≤
      (n : ℝ) * ((2 : ℝ)^slack)⁻¹ := by
  have h := abs_probOutput_toReal_sub_le_tvDist
    (P <$> evalSPMF (runFairBitUniform slack oa)) (P <$> evalSPMF oa)
  have hm := SPMF.tvDist_map_le P (evalSPMF (runFairBitUniform slack oa)) (evalSPMF oa)
  have htv := runFairBitUniform_tv_le slack oa n hb
  simp only [probOutput_map,probEvent_evalSPMF,tvDist,evalSPMF_id] at h
  exact h.trans (hm.trans htv)

/-- The probability loss is retained in extended nonnegative arithmetic. -/
theorem runFairBitUniform_event_loss {A : Type} (slack : Nat) (oa : ProbComp A)
    (n : Nat) (hb : oa.IsTotalQueryBound n) (P : A → Bool) :
    Pr[fun x => P x | oa] - ENNReal.ofReal ((n : ℝ)*((2 : ℝ)^slack)⁻¹) ≤
      Pr[fun x => P x | runFairBitUniform slack oa] := by
  have h := (abs_sub_le_iff.mp (runFairBitUniform_event_error slack oa n hb P)).2
  have hr : Pr[fun x => P x | oa].toReal ≤
      Pr[fun x => P x | runFairBitUniform slack oa].toReal +
        (n : ℝ)*((2 : ℝ)^slack)⁻¹ := by linarith
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal probEvent_ne_top,ENNReal.ofReal_toReal probEvent_ne_top] at he
  exact tsub_le_iff_right.mpr he

#print axioms runFairBitUniform_support_subset
#print axioms runFairBitUniform_event_error
#print axioms runFairBitUniform_event_loss
#print axioms runFairBitUniform_tv_le
end ExplainableCrypto.Helios.Computational
