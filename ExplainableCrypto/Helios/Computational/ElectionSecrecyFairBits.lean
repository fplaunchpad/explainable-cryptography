import ExplainableCrypto.Helios.Computational.ElectionDDHFairBits

/-! Instantiate sampling transport for the complete prepared-election family.
The existing exact reduction query bounds discharge both sampler budgets. -/
namespace ExplainableCrypto.Helios.Computational.ElectionSecrecyFairBits
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionDDHSource
open ElectionSecrecyPrototype

variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)] [∀ n, DecidableEq (G n)]
variable (D : PreparedFamily (fun n => ZMod (q n)) G)

/-- Actual public main reduction with its private sampling replaced by fair bits. -/
noncomputable def main (k n : Nat) : DiffieHellman.DDHAdversary (ZMod (q n)) (G n) :=
  ElectionDDHFairBits.reduction n
    (ballotSecrecyDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n)
      (D.p n+D.c n+9) (accuracy k n))

/-- Actual public rejection reduction, with the same linear statistical slack. -/
noncomputable def reject (n : Nat) : DiffieHellman.DDHAdversary (ZMod (q n)) (G n) :=
  ElectionDDHFairBits.reduction n
    (honestRejectDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n))

/-- Original prepared-election secrecy follows from security of the exact
fair-bit reductions. Sampling loss, both world's transfer and the two full
reduction query budgets are derived. Callback query bounds remain explicit;
neither they nor these DDH-security premises assert standard-PPT execution. -/
theorem prepared_negligible_of_fair_bits (H Q : Polynomial Nat)
    (hhash : ∀ n, D.p n+D.c n ≤ H.eval n)
    (hsize : negligible (fun n => noncePointBound (ZMod (q n))))
    (P C J : Nat → Nat) (hpoly : ∀ n, P n+C n+J n ≤ Q.eval n)
    (hp : ∀ n, (D.prepare n).IsTotalQueryBound (P n))
    (hc : ∀ n initial before, ((D.adversary n initial).castBallot before).IsTotalQueryBound (C n))
    (hj : ∀ n initial saved view,
      ((D.adversary n initial).guessVote saved view).IsTotalQueryBound (J n))
    (hmain : ∀ k, negligible (fun n => ENNReal.ofReal
      (DiffieHellman.ddhDistAdvantage (D.generator n) (main D k n))))
    (hreject : negligible (fun n => ENNReal.ofReal
      (DiffieHellman.ddhDistAdvantage (D.generator n) (reject D n)))) :
    negligible (fun n => ENNReal.ofReal (bias D n)) := by
  apply prepared_negligible_of_ddh D H hhash hsize
  · intro k
    obtain ⟨R, hr⟩ := replay_bounded D H hhash k
    let B := fun n => (1+3*ballotReplayTrials (D.p n+D.c n+9) (accuracy k n))*
      (4*P n+4*C n+78)+(4+4*J n)
    apply ElectionDDHFairBits.negligible_of_bits D.generator
      (fun n => ballotSecrecyDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n)
        (D.p n+D.c n+9) (accuracy k n)) B
      ((1+3*R)*(4*Q+78)+(4+4*Q))
    · intro n
      have hb := hpoly n
      have hpc : 4*P n+4*C n+78 ≤ 4*Q.eval n+78 := by omega
      have hjb : J n ≤ Q.eval n := by omega
      simp only [B, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_one, Polynomial.eval_ofNat]
      exact add_le_add (Nat.mul_le_mul
        (Nat.add_le_add_left (Nat.mul_le_mul_left 3 (hr n)) 1) hpc)
        (Nat.add_le_add_left (Nat.mul_le_mul_left 4 hjb) 4)
    · intro n A T U
      exact ballotSecrecy_prime_cost _ _ _ _ _ _ _ _ _ _ _ _
        (hp n) (hc n) (hj n)
    · exact hmain k
  · apply ElectionDDHFairBits.negligible_of_bits D.generator
      (fun n => honestRejectDistinguisher (D.fingerprint n) (D.prepare n) (D.adversary n))
      (fun n => 4*P n+4*C n+78) (4*Q+78)
    · intro n
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
      have hb := hpoly n
      omega
    · intro n A T U
      exact honestReject_total_bound _ _ _ _ _ _ _ _ _ primeScalarSampler_total_bound (hp n) (hc n)
    · exact hreject

end ExplainableCrypto.Helios.Computational.ElectionSecrecyFairBits
