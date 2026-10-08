import ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototype
import ExplainableCrypto.Helios.Computational.ElectionDDHReductionControls

/-! Controls for the prototype's accuracy quantifiers. The imported finite
controls retain the actual querying election and nonvacuous finite bound. -/
namespace ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototypeControls
open Filter Topology Asymptotics ElectionSecrecyPrototype

/-- Fixed degree one means e=(n+1)^2; exact replay work retains its fourth power. -/
theorem polynomial_accuracy_fixture :
    accuracy 1 2 = 9 ∧ ballotReplayTrials 2 (accuracy 1 2) = 612220032 := by
  decide +kernel

/-- Independently calculated scaled slack at n=2, k=1 is 4/9, below 2/3. -/
theorem scaled_error_fixture :
    (2:ℚ)^1 * (2/(accuracy 1 2:ℚ)) = 4/9 ∧ (4/9:ℚ) < 2/3 := by
  norm_num [accuracy]

/-- Using one fixed linear accuracy for every degree breaks the squeeze bound. -/
theorem fixed_accuracy_breaks_bound :
    ¬ (2:ℚ)^2 * (2/(accuracy 0 2:ℚ)) ≤ 2/(2+1) := by
  norm_num [accuracy]

/-- Stronger negative control: the fixed linear extraction allowance tends to
zero but is not negligible. It cannot be fed to negligible-sum closure. -/
theorem fixed_accuracy_not_negligible :
    ¬ negligible (fun n => ENNReal.ofReal (2/((n:ℝ)+1))) := by
  intro h
  have ht := ((negligible_ofReal_iff (fun n => by positivity)).mp h) 2
  have hev := ht.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num))
  obtain ⟨n, hn, he⟩ := ((eventually_ge_atTop 2).and hev).exists
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (n:ℝ)+1 := by positivity
  have hlarge : 1 ≤ (n:ℝ)^2 * (2/((n:ℝ)+1)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hpos).mpr
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  linarith

end ExplainableCrypto.Helios.Computational.ElectionSecrecyPrototypeControls
