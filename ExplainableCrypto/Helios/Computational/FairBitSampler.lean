import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.IndepProduct
import VCVio.EvalDist.TVDist
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Size

/-! Fixed-width actual fair-bit sampling, followed by explicit modulo reduction. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

/-- Read w independent bits and encode them using Mathlib's little-endian
binary-digit equivalence. This calls only the fair-bit oracle. -/
def sampleFairBitIndex (w : Nat) : OracleComp coinSpec (Fin (2^w)) :=
  finFunctionFinEquiv <$> Fin.mOfFn w (fun _ => finTwoEquiv.symm <$> coin)

/-- Exact uniformity holds for the power-of-two intermediate range. -/
theorem sampleFairBitIndex_probability (w : Nat) (x : Fin (2^w)) :
    Pr[= x | sampleFairBitIndex w] = ((2^w : Nat) : ENNReal)⁻¹ := by
  rw [sampleFairBitIndex,probOutput_map_equiv,probOutput_mOfFn]
  simp only [probOutput_map_equiv,probOutput_coin,Finset.prod_const,Finset.card_univ,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  rw [ENNReal.inv_pow]

/-- The actual bit-reading program uses at most w coin queries. This counts
queries, not the arithmetic or finite-function encoding cost. -/
theorem sampleFairBitIndex_query_bound (w : Nat) :
    (sampleFairBitIndex w).IsTotalQueryBound w := by
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  induction w with
  | zero => trivial
  | succ w ih =>
    simp only [Fin.mOfFn,bind_pure_comp]
    have hc : (finTwoEquiv.symm <$> coin).IsTotalQueryBound 1 := by
      simp [coin,IsTotalQueryBound]
    have hr (a : Fin 2) :
        ((@Fin.cons w (fun _ => Fin 2) a) <$> Fin.mOfFn w (fun _ => finTwoEquiv.symm <$> coin)).IsTotalQueryBound w :=
      (isQueryBound_map_iff _ _ _ _ _).mpr ih
    exact (isTotalQueryBound_bind hc hr).mono (by omega)

/-- Range reduction is executable and always returns an in-range value. -/
def sampleFairBitModulo (q w : Nat) [NeZero q] : OracleComp coinSpec (Fin q) :=
  (fun x : Fin (2^w) => (⟨x.val % q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩ : Fin q))
    <$> sampleFairBitIndex w

/-- Modulo conversion introduces no additional coin query. -/
theorem sampleFairBitModulo_query_bound (q w : Nat) [NeZero q] :
    (sampleFairBitModulo q w).IsTotalQueryBound w :=
  (isQueryBound_map_iff _ _ _ _ _).mpr (sampleFairBitIndex_query_bound w)

private theorem sum_mod_blocks (q d : Nat) (f : Nat → ENNReal) :
    (∑ i ∈ Finset.range (d*q),f (i%q)) =
      (d : ENNReal) * ∑ i ∈ Finset.range q,f (i%q) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih]
    simp [Nat.add_mod,Nat.cast_add,Nat.cast_one,add_mul]

private theorem sum_mod_range (q M : Nat) [NeZero q] (f : Nat → ENNReal) :
    (∑ i ∈ Finset.range M,f (i%q)) =
      (M/q : Nat) * (∑ i ∈ Finset.range q,f i) + ∑ i ∈ Finset.range (M%q),f i := by
  have hq := Nat.pos_of_ne_zero (NeZero.ne q)
  have he : M = M/q*q + M%q := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hblock : (∑ i ∈ Finset.range q,f (i%q)) = ∑ i ∈ Finset.range q,f i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
  have htail : (∑ i ∈ Finset.range (M%q),f ((M/q*q+i)%q)) =
      ∑ i ∈ Finset.range (M%q),f i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiq := (Finset.mem_range.mp hi).trans (Nat.mod_lt M hq)
    simp [Nat.add_mod,Nat.mod_eq_of_lt hiq]
  calc
    _ = ∑ i ∈ Finset.range (M/q*q+M%q),f (i%q) := by conv_lhs => rw [he]
    _ = _ := by rw [Finset.sum_range_add,sum_mod_blocks,hblock,htail]

/-- Exact residue probabilities, including the extra occurrence in the final
incomplete block. No exact uniformity is asserted for a general modulus. -/
theorem sampleFairBitModulo_probability (q w : Nat) [NeZero q] (y : Fin q) :
    Pr[= y | sampleFairBitModulo q w] =
      (((2^w/q : Nat) : ENNReal) + if y.val < 2^w%q then 1 else 0) *
        ((2^w : Nat) : ENNReal)⁻¹ := by
  rw [sampleFairBitModulo,probOutput_map_eq_sum_fintype_ite]
  simp only [sampleFairBitIndex_probability,Fin.ext_iff]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => if y.val = i%q then ((2^w : Nat) : ENNReal)⁻¹ else 0) (2^w)]
  rw [sum_mod_range q (2^w) (fun i => if y.val = i then ((2^w : Nat) : ENNReal)⁻¹ else 0)]
  simp only [Finset.sum_ite_eq,Finset.mem_range,if_pos y.isLt]
  split_ifs <;> simp [add_mul]

private theorem sum_mod_refill (q M : Nat) [NeZero q] (y : Fin q) (a b : ENNReal) :
    (∑ i ∈ Finset.range M,
      if i < M/q*q then (if y.val = i%q then a else 0) else b) =
        (M/q : Nat) * a + (M%q : Nat) * b := by
  have he : M = M/q*q + M%q := by rw [Nat.mul_comm,Nat.div_add_mod]
  rw [show Finset.range M = Finset.range (M/q*q+M%q) from congrArg Finset.range he]
  rw [Finset.sum_range_add]
  have hp : (∑ i ∈ Finset.range (M/q*q),
      if i < M/q*q then (if y.val = i%q then a else 0) else b) =
        ∑ i ∈ Finset.range (M/q*q),if y.val = i%q then a else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  have ht : (∑ i ∈ Finset.range (M%q),
      if M/q*q+i < M/q*q then (if y.val = (M/q*q+i)%q then a else 0) else b) =
        (M%q : Nat) * b := by
    simp
  rw [hp,ht,sum_mod_blocks q (M/q) (fun i => if y.val = i then a else 0)]
  have hu : (∑ i ∈ Finset.range q,if y.val = i%q then a else 0) = a := by
    calc
      _ = ∑ i ∈ Finset.range q,if y.val = i then a else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]
      _ = a := by simp [y.isLt]
  rw [hu]

private theorem refill_weight (q M : Nat) [NeZero q] (hM : 0 < M) :
    ((M/q : Nat) : ENNReal) * (M : ENNReal)⁻¹ +
      ((M%q : Nat) : ENNReal) * ((M : ENNReal)⁻¹ * (q : ENNReal)⁻¹) =
        (q : ENNReal)⁻¹ := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hM
  have he : (q : ℝ) * (M/q : Nat) + (M%q : Nat) = M := by
    exact_mod_cast Nat.div_add_mod M q
  have hme : (M : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hM
  have hqe : (q : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hmi : (M : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hme
  have hqi : (q : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hqe
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_natCast]
  field_simp
  nlinarith

private def moduloRefill (q w : Nat) [NeZero q] : ProbComp (Fin q) := do
  let x ← uniformSample (Fin (2^w))
  if x.val < 2^w/q*q then
    pure ⟨x.val%q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩
  else uniformSample (Fin q)

private theorem moduloRefill_eq (q w : Nat) [NeZero q] :
    evalSPMF (moduloRefill q w) = evalSPMF (uniformSample (Fin q)) := by
  apply evalSPMF_ext
  intro y
  rw [moduloRefill,probOutput_bind_eq_tsum]
  have hp (x : Fin (2^w)) :
      Pr[= y | (if x.val < 2^w/q*q then
        pure (⟨x.val%q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩ : Fin q)
        else uniformSample (Fin q) : ProbComp (Fin q))] =
          if x.val < 2^w/q*q then (if y.val = x.val%q then 1 else 0)
          else (q : ENNReal)⁻¹ := by
    split_ifs <;> simp_all only [probOutput_pure,probOutput_uniformSample,Fintype.card_fin,Fin.ext_iff,ite_true,ite_false]
  simp_rw [hp,probOutput_uniformSample,Fintype.card_fin]
  rw [tsum_fintype]
  simp only [mul_ite,mul_one,mul_zero]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < 2^w/q*q then
    (if y.val = i%q then ((2^w : Nat) : ENNReal)⁻¹ else 0)
    else ((2^w : Nat) : ENNReal)⁻¹ * (q : ENNReal)⁻¹) (2^w)]
  rw [sum_mod_refill,refill_weight q (2^w) (by positivity)]

private theorem uniformIndex_tail (q w : Nat) [NeZero q] :
    Pr[fun x : Fin (2^w) => ¬ x.val < 2^w/q*q | uniformSample (Fin (2^w))] =
      ((2^w%q : Nat) : ENNReal) * ((2^w : Nat) : ENNReal)⁻¹ := by
  rw [probEvent_eq_tsum_ite,tsum_fintype]
  simp only [probOutput_uniformSample,Fintype.card_fin,ite_not]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    if i < 2^w/q*q then 0 else ((2^w : Nat) : ENNReal)⁻¹) (2^w)]
  have h := sum_mod_refill q (2^w) (0 : Fin q) 0 ((2^w : Nat) : ENNReal)⁻¹
  simpa only [ite_self,mul_zero,zero_add] using h

/-- The actual fair-bit modulo sampler is within the incomplete-block mass of
ideal uniform sampling. This compares the complete output laws. -/
theorem sampleFairBitModulo_tv_le (q w : Nat) [NeZero q] :
    SPMF.tvDist (evalSPMF (sampleFairBitModulo q w))
      (evalSPMF (uniformSample (Fin q))) ≤
        (2^w%q : Nat) / (2^w : ℝ) := by
  let modFn (x : Fin (2^w)) : Fin q :=
    ⟨x.val%q,Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne q))⟩
  let f (x : Fin (2^w)) : ProbComp (Fin q) := pure (modFn x)
  let g (x : Fin (2^w)) : ProbComp (Fin q) :=
    if x.val < 2^w/q*q then f x else uniformSample (Fin q)
  have hi : evalSPMF (sampleFairBitIndex w) = evalSPMF (uniformSample (Fin (2^w))) := by
    apply evalSPMF_ext
    intro x
    simp only [sampleFairBitIndex_probability,probOutput_uniformSample,Fintype.card_fin]
  have he : evalSPMF (sampleFairBitModulo q w) =
      evalSPMF (uniformSample (Fin (2^w)) >>= f) := by
    unfold sampleFairBitModulo
    rw [evalSPMF_map,hi]
    simp only [evalSPMF_bind,f,evalSPMF_pure,map_eq_bind_pure_comp]
    rfl
  have h := tvDist_bind_left_event_le (uniformSample (Fin (2^w))) f g
    (fun x => ¬ x.val < 2^w/q*q) (by intro x hx; simp_all [g])
  have hg : uniformSample (Fin (2^w)) >>= g = moduloRefill q w := rfl
  rw [hg] at h
  unfold tvDist at h
  rw [moduloRefill_eq,← he] at h
  rw [uniformIndex_tail,ENNReal.toReal_mul,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,ENNReal.toReal_natCast] at h
  simpa only [Nat.cast_pow,Nat.cast_ofNat,div_eq_mul_inv] using h

/-- Use the range's binary width plus an explicit statistical slack. -/
def sampleFairBitRange (q slack : Nat) [NeZero q] : OracleComp coinSpec (Fin q) :=
  sampleFairBitModulo q (q.size+slack)

/-- Extra bits make the sampling error at most 2^(-slack), for every positive
range size, including adaptive range arguments. -/
theorem sampleFairBitRange_tv_le (q slack : Nat) [NeZero q] :
    SPMF.tvDist (evalSPMF (sampleFairBitRange q slack))
      (evalSPMF (uniformSample (Fin q))) ≤ ((2 : ℝ)^slack)⁻¹ := by
  have hr : ((2^(q.size+slack)%q : Nat) : ℝ) ≤ q := by
    exact_mod_cast (Nat.mod_lt (2^(q.size+slack)) (Nat.pos_of_ne_zero (NeZero.ne q))).le
  have hq : (q : ℝ) ≤ (2 : ℝ)^q.size := by exact_mod_cast (Nat.lt_size_self q).le
  calc
    _ ≤ (2^(q.size+slack)%q : Nat) / (2^(q.size+slack) : ℝ) :=
      sampleFairBitModulo_tv_le q (q.size+slack)
    _ ≤ (q : ℝ) / (2^(q.size+slack) : ℝ) :=
      div_le_div_of_nonneg_right hr (by positivity)
    _ ≤ (2 : ℝ)^q.size / (2^(q.size+slack) : ℝ) :=
      div_le_div_of_nonneg_right hq (by positivity)
    _ = _ := by rw [pow_add]; field_simp

/-- The bound covers the entire output of any common probabilistic continuation,
including its observations and retained state. -/
theorem sampleFairBitRange_bind_tv_le {A : Type} (q slack : Nat) [NeZero q]
    (K : Fin q → SPMF A) :
    SPMF.tvDist (evalSPMF (sampleFairBitRange q slack) >>= K)
      (evalSPMF (uniformSample (Fin q)) >>= K) ≤ ((2 : ℝ)^slack)⁻¹ :=
  (SPMF.tvDist_bind_right_le K _ _).trans (sampleFairBitRange_tv_le q slack)

/-- This is a fair-bit query count; local encoding and arithmetic costs are separate. -/
theorem sampleFairBitRange_query_bound (q slack : Nat) [NeZero q] :
    (sampleFairBitRange q slack).IsTotalQueryBound (q.size+slack) :=
  sampleFairBitModulo_query_bound q (q.size+slack)

#print axioms sampleFairBitRange_tv_le
#print axioms sampleFairBitRange_bind_tv_le
#print axioms sampleFairBitRange_query_bound
#print axioms sampleFairBitModulo_tv_le
#print axioms sampleFairBitModulo_probability
#print axioms sampleFairBitIndex_probability
#print axioms sampleFairBitIndex_query_bound
#print axioms sampleFairBitModulo_query_bound
end ExplainableCrypto.Helios.Computational
