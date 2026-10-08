import ExplainableCrypto.Helios.Computational.ElectionDDHPrefix
import ExplainableCrypto.Helios.Computational.BallotReplayRepeat

/-! Repeated extraction for the actual public-challenge prefix. Its first output,
preparation/casting states and live cache survive even when no witness is found. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]
local instance prefixRepeatInhabited : Inhabited F := ⟨0⟩
noncomputable local instance prefixRepeatUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

noncomputable def prefixRepeated {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n k : Nat) :=
  ballotJointReplayRetained (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk) n k

/-- Actual accepted-prefix failure, including the charged low-context event.
The original execution is neither replaced nor conditioned on success. -/
theorem prefix_failure_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (p c k : Nat) (hp : prepare.IsQueryBoundP (ElectionQueryBound.isBallot (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionQueryBound.isBallot (F := F)) c) (δ : ENNReal) :
    Pr[fun out => PrefixAccepted out.1.1 ∧ out.2 = none |
      prefixRepeated fingerprint g pk A T prepare adversary (p+c+9) k] ≤
      3*(p+c+9+1 : ENNReal)*δ + (1-(δ-(Fintype.card F : ENNReal)⁻¹)^3)^k := by
  have hs := ballotJointReplay_selector_eq
    (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk)
    (p+c+9) PrefixAccepted (prefix_bound fingerprint g pk A T prepare adversary p c hp hc)
    (prefix_trace_verified fingerprint g pk A T hg prepare adversary)
  have h := ballotJointReplayRetained_failure_le
    (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk) (p+c+9) k δ
    PrefixAccepted (fun path ha i => by rw [hs path i]; exact decide_eq_true ha)
  simpa only [prefixRepeated,Nat.cast_add,Nat.cast_ofNat] using h

/-- Exact original output/live-cache distribution, on all rejection and
extraction-failure branches as well as success. No acceptance premise. -/
theorem prefix_repeated_original {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n k : Nat) :
    evalSPMF (Prod.fst <$> prefixRepeated fingerprint g pk A T prepare adversary n k) =
      evalSPMF (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅) :=
  ballotJointReplayRetained_original _ _ n k

/-- Valid witnesses, actual original cache membership and derived private/live
consistency are returned together, ready for the finishing phase. -/
theorem prefix_repeated_valid {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : g ≠ 0) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (n k : Nat) (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (w : Option (Fin 2) → BallotWitness F)
    (ho : (out,some w) ∈ support (prefixRepeated fingerprint g pk A T prepare adversary n k)) :
    PrefixAccepted out.1 ∧ (∀ i, (out.1.1.submission.coveredStatement g pk i).Witnesses (w i)) ∧
      ElectionProgrammedSource.Inv out.1.2 out.2 ∧
      out ∈ support (runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅) := by
  obtain ⟨hr,hv⟩ := ballotJointReplayRetained_valid
    (prefixSource fingerprint g pk A T prepare adversary) (prefixSelect g pk) n k out w ho
  have ha : PrefixAccepted out.1 := by
    by_contra hn
    obtain ⟨c,hv⟩ := (hv none).2
    simp only [prefixSelect,if_neg hn,Ballot.coveredStatement] at hv
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hv.1.1.symm)
  exact ⟨ha,fun i => (hv i).1,prefix_inv fingerprint g pk A T prepare adversary out hr,hr⟩

/-- Consistent nonces and vote counts refer to the retained original ballot. -/
theorem prefix_repeated_consistent {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0)
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (n k : Nat)
    (out : PrefixOutput F G Init Saved × BallotOracleCache F G)
    (w : Option (Fin 2) → BallotWitness F)
    (ho : (out,some w) ∈ support (prefixRepeated fingerprint g pk A T prepare adversary n k)) :
    PrefixAccepted out.1 ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    exact one_ne_zero (hg (by simp [he]) : (1 : F) = 0)
  obtain ⟨ha,hw,_⟩ := prefix_repeated_valid fingerprint g pk A T hg0 prepare adversary n k out w ho
  exact ⟨ha,(out.1.1.submission.covered_witnesses_sum g pk hg w hw).1,
    out.1.1.submission.covered_witnesses_atMostOne g pk hg h2 w hw⟩

omit [Fintype F] in
/-- Structural interaction cost, including private randomness. The supplied
complete-source bound and pure-operation/runtime costs remain distinct from the
live ballot-hash bound used by `prefix_failure_le`. -/
theorem prefix_repeated_query_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (n k m : Nat) (hm : (prefixSource fingerprint g pk A T prepare adversary).IsTotalQueryBound m) :
    (prefixRepeated fingerprint g pk A T prepare adversary n k).IsTotalQueryBound ((1+3*k)*m) :=
  ballotJointReplayRetained_total_query_bound _ _ n k m hm

#print axioms prefix_failure_le
#print axioms prefix_repeated_original
#print axioms prefix_repeated_valid
#print axioms prefix_repeated_consistent
#print axioms prefix_repeated_query_bound
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
