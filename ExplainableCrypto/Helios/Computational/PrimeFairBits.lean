import ExplainableCrypto.Helios.Computational.PrimeReplayCost
import ExplainableCrypto.Helios.Computational.FairBitUniformOracle

/-! Actual fair-bit implementation of the explicit-source joint extractor.
Its sampling loss is explicit; local-operation and machine costs remain open. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {q : Nat} [Fact q.Prime] {G : Type} [AddCommGroup G]
  [Module (ZMod q) G] [DecidableEq G]
attribute [local irreducible] repairedSubmissionPrimeBits_extract
local instance primeFairBitsInhabited : Inhabited (ZMod q) := ⟨0⟩
noncomputable local instance primeFairBitsUniform : IsUniformSpec ((Unit →ₒ ZMod q) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

private def primeEntropyProgram {A : Type}
    (oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) A) : ProbComp A :=
  simulateQ ballotForkEntropyImpl oa

private theorem primeEntropyProgram_eval {A : Type}
    (oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) A) :
    evalSPMF (primeEntropyProgram oa) = evalSPMF oa := ballotFork_entropy_eval oa

private theorem primeEntropyProgram_bound {A : Type}
    (oa : OracleComp (FiatShamir.Fork.wrappedSpec (ZMod q)) A)
    (n : Nat) (h : oa.IsTotalQueryBound n) : (primeEntropyProgram oa).IsTotalQueryBound n := by
  apply h.simulateQ_of_step
  rintro (t | u)
  · simp [ballotForkEntropyImpl,QueryImpl.add,IsTotalQueryBound]
  · exact primeScalarSampler_total_bound


/-- Replace every actual uniform request, including adaptive attacker and replay
requests, by finite fair-bit sampling. No new abort or rejection branch is added. -/
def repairedSubmissionFairBits_extract (slack : Nat) (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) :=
  runFairBitUniform slack (primeEntropyProgram (repairedSubmissionPrimeBits_extract g pk vote attacker n))

/-- The complete extractor output law, including failure, has this explicit
sampling distance from the proved ideal-range extractor. -/
theorem repairedSubmissionFairBits_extract_tv_le (slack : Nat) (g pk : G) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n m : Nat) (hb : ∀ view, (attacker view).IsTotalQueryBound m) :
    SPMF.tvDist (evalSPMF (repairedSubmissionFairBits_extract slack g pk vote attacker n))
      (evalSPMF (repairedSubmissionPrimeBits_extract g pk vote attacker n)) ≤
        (16*(m+19) : ℝ)*((2 : ℝ)^slack)⁻¹ := by
  have h := runFairBitUniform_tv_le slack
    (primeEntropyProgram (repairedSubmissionPrimeBits_extract g pk vote attacker n))
    (16*(m+19)) (primeEntropyProgram_bound _ _
      (repairedSubmissionPrimeBits_extract_total_bound g pk vote attacker n m hb))
  rw [primeEntropyProgram_eval] at h
  simpa only [repairedSubmissionFairBits_extract,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using h

/-- Every returned witness remains valid for the retained accepting ballot.
Support transport is derived from actual finite-range answers, not assumed. -/
theorem repairedSubmissionFairBits_extract_valid (slack : Nat) (g pk : G) (hg : g ≠ 0)
    (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (result : RepairedSubmissionResult (ZMod q) G)
    (w : Option (Fin 2) → BallotWitness (ZMod q))
    (ho : some (result,w) ∈ support (repairedSubmissionFairBits_extract slack g pk vote attacker n)) :
    result.Accepted ∧ (∀ i, (result.ballot.coveredStatement g pk i).Witnesses (w i)) ∧
      ∃ cache, (result,cache) ∈ support
        (runBallotOracle (repairedSubmissionPrimeSourceOracle g pk vote attacker) ∅) :=
  repairedSubmissionPrimeBits_extract_valid g pk hg vote attacker n result w
    ((mem_support_iff_of_evalSPMF_eq (primeEntropyProgram_eval _) _).mp
      (runFairBitUniform_support_subset slack _ ho))

/-- The actual fair-bit extractor retains aggregate nonce consistency and the
historical integer at-most-one constraint at prime modulus q>2. -/
theorem repairedSubmissionFairBits_extract_consistent (slack : Nat) (g pk : G)
    (hg : Function.Injective (fun r : ZMod q => r • g)) (hq : 2 < q) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n : Nat) (result : RepairedSubmissionResult (ZMod q) G)
    (w : Option (Fin 2) → BallotWitness (ZMod q))
    (ho : some (result,w) ∈ support (repairedSubmissionFairBits_extract slack g pk vote attacker n)) :
    result.Accepted ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 :=
  repairedSubmissionPrimeBits_extract_consistent g pk hg hq vote attacker n result w
    ((mem_support_iff_of_evalSPMF_eq (primeEntropyProgram_eval _) _).mp
      (runFairBitUniform_support_subset slack _ ho))

/-- The historical joint-extraction bound loses only the proved fair-bit
sampling term. All subtractions use ENNReal truncated subtraction. -/
theorem repairedSubmissionFairBits_extract_le (slack : Nat) (g pk : G)
    (hg : Function.Injective (fun r : ZMod q => r • g)) (vote : Bool)
    (attacker : HonestPrefixView (ZMod q) G → BallotOracleComp (ZMod q) G (Ballot (ZMod q) G 2))
    (n m : Nat)
    (hh : ∀ view, (attacker view).IsQueryBoundP (isBallotHashQuery (F := ZMod q)) n)
    (hb : ∀ view, (attacker view).IsTotalQueryBound m) (δ : ENNReal) :
    let accepted := Pr[fun out => out.1.1.decision = .accepted |
      runBallotProgrammed g pk (repairedSubmissionOracle g pk vote attacker)]
    let a := accepted - (9 * noncePointBound (ZMod q) + ENNReal.ofReal (90 / (q : ℝ)))
    (a - 3*(n+16 : ENNReal)*δ) * (δ - (q : ENNReal)⁻¹)^3 -
      ENNReal.ofReal ((16*(m+19) : ℝ)*((2 : ℝ)^slack)⁻¹) ≤
        Pr[fun out => out.isSome | repairedSubmissionFairBits_extract slack g pk vote attacker n] := by
  have h := runFairBitUniform_event_loss slack
    (primeEntropyProgram (repairedSubmissionPrimeBits_extract g pk vote attacker n)) (16*(m+19))
    (primeEntropyProgram_bound _ _
      (repairedSubmissionPrimeBits_extract_total_bound g pk vote attacker n m hb)) Option.isSome
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (primeEntropyProgram_eval _)] at h
  have hs := tsub_le_tsub_right (repairedSubmissionPrimeBits_extract_le g pk hg vote attacker n hh δ)
    (ENNReal.ofReal ((16*(m+19) : ℝ)*((2 : ℝ)^slack)⁻¹))
  exact hs.trans (by simpa only [repairedSubmissionFairBits_extract,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using h)

#print axioms repairedSubmissionFairBits_extract_tv_le
#print axioms repairedSubmissionFairBits_extract_valid
#print axioms repairedSubmissionFairBits_extract_consistent
#print axioms repairedSubmissionFairBits_extract_le
end ExplainableCrypto.Helios.Computational
