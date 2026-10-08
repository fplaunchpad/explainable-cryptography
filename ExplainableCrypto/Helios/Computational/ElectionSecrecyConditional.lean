import ExplainableCrypto.Helios.Computational.ReductionEfficiency

/-! Conditional secrecy under explicitly named efficiency hypotheses for the exact reductions.
All existing prepared-family, field-size, and callback query assumptions remain unchanged.
The DDH hypothesis is for the concrete finite three-tape fair-coin model in ReductionEfficiency;
standard-machine equivalence is an external argument, not an additional proved adequacy claim.
-/
namespace ExplainableCrypto.Helios.Computational.ElectionSecrecyConditional
open OracleComp OracleSpec ElectionOracle ElectionCache ElectionSecrecyPrototype
open ReductionEfficiency

attribute [local irreducible] ElectionSecrecyFairBits.main ElectionSecrecyFairBits.reject

variable {q : Nat → Nat} [∀ n, Fact (q n).Prime] {G : Nat → Type}
  [∀ n, AddCommGroup (G n)] [∀ n, Module (ZMod (q n)) (G n)]
  [∀ n, DecidableEq (G n)]

/-- The original secrecy conclusion, conditional on DDH in the chosen concrete machine model
and externally supplied execution/correspondence/runtime witnesses for both exact reductions.
In particular, callback bounds quantify every input shown here, not merely reached inputs.
This theorem does not infer those bounds from an attacker's ordinary input-length PPT bound.
-/
theorem prepared_negligible_of_native_coin_ddh
    (D : PreparedFamily (fun n => ZMod (q n)) G)
    (representation : GroupRepresentation G)
    (H Q : Polynomial Nat)
    (hhash : ∀ n, D.p n + D.c n ≤ H.eval n)
    (hsize : negligible (fun n => noncePointBound (ZMod (q n))))
    (P C J : Nat → Nat) (hpoly : ∀ n, P n + C n + J n ≤ Q.eval n)
    (hp : ∀ n, (D.prepare n).IsTotalQueryBound (P n))
    (hc : ∀ n initial before,
      ((D.adversary n initial).castBallot before).IsTotalQueryBound (C n))
    (hj : ∀ n initial saved view,
      ((D.adversary n initial).guessVote saved view).IsTotalQueryBound (J n))
    (hmain : MainReductionEfficient D representation)
    (hreject : RejectionReductionEfficient D representation)
    (hddh : DDHAssumption (q := q) representation D.generator) :
    negligible (fun n => ENNReal.ofReal (bias D n)) := by
  apply ElectionSecrecyFairBits.prepared_negligible_of_fair_bits D H Q hhash hsize
    P C J hpoly hp hc hj
  · intro k
    exact hddh (fun n challenge => ElectionSecrecyFairBits.main D k n
      challenge.1 challenge.2.1 challenge.2.2.1 challenge.2.2.2) (hmain k)
  · exact hddh (fun n challenge => ElectionSecrecyFairBits.reject D n
      challenge.1 challenge.2.1 challenge.2.2.1 challenge.2.2.2) hreject

#print axioms prepared_negligible_of_native_coin_ddh
end ExplainableCrypto.Helios.Computational.ElectionSecrecyConditional
