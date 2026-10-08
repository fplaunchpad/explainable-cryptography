import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.QueryBound
import Mathlib.Data.Nat.Prime.Basic

/-! Exact finite fair-coin programs have dyadic probabilities. This obstructs
exact realization of historical odd-prime scalar sampling in this representation. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec

/-- Finite binary branching gives a derived maximum coin count for every actual
terminating coin program, even when the caller supplies no budget. -/
theorem coinProgram_has_bound {A : Type} (oa : OracleComp coinSpec A) :
    ∃ n : Nat, oa.IsTotalQueryBound n := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact ⟨0,trivial⟩
  | query_bind t next ih =>
    obtain ⟨nf,hf⟩ := ih false
    obtain ⟨nt,ht⟩ := ih true
    refine ⟨max nf nt + 1,?_⟩
    rw [isTotalQueryBound_query_bind_iff]
    refine ⟨by omega,?_⟩
    intro answer
    cases answer
    · exact hf.mono (by omega)
    · exact ht.mono (by omega)

private theorem coin_bind_probability {A : Type} (next : Bool → OracleComp coinSpec A) (x : A) :
    Pr[= x | coin >>= next] =
      (Pr[= x | next false] + Pr[= x | next true]) * (2 : ENNReal)⁻¹ := by
  rw [probOutput_bind_eq_tsum]
  simp [tsum_fintype,probOutput_coin,mul_add,mul_comm,add_comm]

/-- A bounded actual coin computation has an integer numerator over 2^n. -/
theorem coinProgram_dyadic {A : Type} (oa : OracleComp coinSpec A) (n : Nat)
    (hb : oa.IsTotalQueryBound n) (x : A) :
    ∃ k : Nat, Pr[= x | oa] * (2 : ENNReal)^n = (k : ENNReal) := by
  let : DecidableEq A := Classical.typeDecidableEq A
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a =>
    rcases Classical.em (x = a) with h | h
    · subst x
      exact ⟨2^n,by simp⟩
    · exact ⟨0,by simp [h]⟩
  | query_bind t next ih =>
    rw [isTotalQueryBound_query_bind_iff] at hb
    cases n with
    | zero => omega
    | succ n =>
      obtain ⟨kf,hf⟩ := ih false n (by simpa using hb.2 false)
      obtain ⟨kt,ht⟩ := ih true n (by simpa using hb.2 true)
      refine ⟨kf+kt,?_⟩
      cases t
      change Pr[= x | coin >>= next] * (2 : ENNReal)^(n+1) = _
      rw [coin_bind_probability,pow_succ]
      calc
        _ = (Pr[= x | next false]+Pr[= x | next true]) * (2 : ENNReal)^n * (2⁻¹*2) := by ac_rfl
        _ = (Pr[= x | next false]+Pr[= x | next true]) * (2 : ENNReal)^n := by
          rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤),mul_one]
        _ = _ := by rw [add_mul,hf,ht]; simp

/-- No terminating coin-only program has a point of mass 1/q for an odd prime q.
The query bound is derived from the actual program, not assumed by the caller. -/
theorem coinProgram_not_prime_uniform {A : Type} (oa : OracleComp coinSpec A)
    (q : Nat) (hq : q.Prime) (hodd : 2 < q) (x : A) :
    Pr[= x | oa] ≠ (q : ENNReal)⁻¹ := by
  intro h
  obtain ⟨n,hb⟩ := coinProgram_has_bound oa
  obtain ⟨k,hk⟩ := coinProgram_dyadic oa n hb x
  rw [h] at hk
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne_zero
  have he : (2 : ENNReal)^n = (k : ENNReal) * q := by
    calc
      _ = (2 : ENNReal)^n * ((q : ENNReal)⁻¹ * q) := by
        rw [ENNReal.inv_mul_cancel hq0 (by simp),mul_one]
      _ = ((q : ENNReal)⁻¹ * (2 : ENNReal)^n) * q := by ac_rfl
      _ = _ := by rw [hk]
  have hn : 2^n = k*q := by exact_mod_cast he
  have hd : q ∣ 2^n := ⟨k,by rw [hn,Nat.mul_comm]⟩
  have hle := Nat.le_of_dvd (by decide : 0 < 2) (hq.dvd_of_dvd_pow hd)
  omega

#print axioms coinProgram_not_prime_uniform
#print axioms coinProgram_has_bound
#print axioms coinProgram_dyadic
end ExplainableCrypto.Helios.Computational
