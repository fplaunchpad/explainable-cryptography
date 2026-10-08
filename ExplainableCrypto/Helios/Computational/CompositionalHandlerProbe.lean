import VCVio.CryptoFoundations.Asymptotics.OracleClosure
import Mathlib.Analysis.SpecificLimits.Normed

/-! A resource-contract falsifier, not a counterexample to PPT composition.
The consumer below makes n calls but has exponentially growing query/output
words. No StrictPPTWitness is asserted for that consumer or fabricated for the
handler. This is not a claim about actual Helios state growth. -/
namespace ExplainableCrypto.Helios.Computational.CompositionalHandlerProbe
open PFunctor OracleComp.Complexity OracleSpec

abbrev wordSpec : OracleSpec (List Bool) := fun _ => List Bool

def doubleHandler (word : List Bool) : FreeM emptySpec.toPFunctor (List Bool) :=
  pure (word ++ word)

def consumer : Nat → List Bool → FreeM wordSpec.toPFunctor (List Bool)
  | 0, word => pure word
  | n+1, word => FreeM.liftBind word (consumer n)

def expanded : Nat → List Bool → List Bool
  | 0, word => word
  | n+1, word => expanded n (word ++ word)

/-- Actual typed handler substitution, with no host-side answer oracle. -/
theorem closed_consumer (n : Nat) (word : List Bool) :
    closeHandler doubleHandler (consumer n word) = pure (expanded n word) := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih =>
    simpa only [consumer,closeHandler_liftBind,doubleHandler,pure_bind,expanded] using
      ih (word ++ word)

/-- The allowed-reply policy is total, so the leaf premise is not vacuous. -/
theorem handler_conforms (word : List Bool) :
    (doubleHandler word).LeavesSatisfyUnder (fun _ _ => True)
      (fun reply => reply.length = 2*word.length) := by
  simp [doubleHandler,FreeM.LeavesSatisfyUnder,List.length_append]
  omega

theorem consumer_leaves (n : Nat) (word : List Bool) :
    (consumer n word).LeavesSatisfyUnder (fun _ _ => True) (fun _ => True) := by
  induction n generalizing word with
  | zero => trivial
  | succ n ih => exact fun reply _ => ih reply

/-- The existing generic WP fold counts exactly n handler calls along the
actual deterministic doubled-reply path. -/
theorem consumer_call_count (n : Nat) (word : List Bool) :
    FreeM.wpFold (P := wordSpec.toPFunctor) (fun word next => 1 + next (word ++ word))
      (consumer n word) (fun _ => 0) = n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih =>
    change 1 + FreeM.wpFold (P := wordSpec.toPFunctor)
      (fun word next => 1 + next (word ++ word))
      (consumer n (word ++ word)) (fun _ => 0) = n+1
    rw [ih]
    omega

/-- Exact general state-growth witness: n calls, but not an n-sized handoff. -/
theorem expanded_length (n : Nat) (word : List Bool) :
    (expanded n word).length = 2^n*word.length := by
  induction n generalizing word with
  | zero => simp [expanded]
  | succ n ih => simp only [expanded,ih,List.length_append,pow_succ]; ring

/-- Independently literal positive and nearby invalid handoff bound. -/
theorem four_calls_literal : expanded 4 [false] = List.replicate 16 false := rfl

theorem eight_calls_not_quadratic :
    (expanded 8 [false]).length = 256 ∧ ¬ (expanded 8 [false]).length ≤ 8^2 := by
  norm_num [expanded_length]

/-- Every fixed monomial envelope is exceeded; standard eventual exponential
separation is reused, not a new asymptotics development. -/
theorem no_fixed_monomial (C d : Nat) :
    ∃ n : Nat, C*n^d < (expanded n [false]).length := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d (by norm_num : (1:ℝ)<2)).bound
    (show 0 < (1 / ((C:ℝ)+1)) by positivity)
  obtain ⟨n, hn⟩ := Filter.Eventually.exists h
  have hn' : (n:ℝ)^d ≤ 2^n / ((C:ℝ)+1) := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ)^d by positivity),
      abs_of_nonneg (show (0:ℝ) ≤ (2:ℝ)^n by positivity),
      one_div,div_eq_mul_inv,mul_comm,one_mul] using hn
  have hp : (0:ℝ) < 2^n := by positivity
  have hc : (0:ℝ) < (C:ℝ)+1 := by positivity
  have hh : ((C:ℝ)+1)*(n:ℝ)^d ≤ 2^n := by
    have := (le_div_iff₀ hc).mp hn'
    nlinarith
  refine ⟨n,?_⟩
  rw [expanded_length]
  simp only [List.length_singleton,Nat.mul_one]
  have hlt : (C:ℝ)*(n:ℝ)^d < 2^n := by
    by_cases hz : (n:ℝ)^d = 0
    · simp [hz,hp]
    · have hzpos : 0 < (n:ℝ)^d := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      nlinarith
  exact_mod_cast hlt

#print axioms closed_consumer
#print axioms handler_conforms
#print axioms consumer_leaves
#print axioms consumer_call_count
#print axioms expanded_length
#print axioms four_calls_literal
#print axioms eight_calls_not_quadratic
#print axioms no_fixed_monomial
end ExplainableCrypto.Helios.Computational.CompositionalHandlerProbe
