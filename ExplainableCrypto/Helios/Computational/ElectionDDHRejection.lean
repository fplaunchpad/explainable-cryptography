import ExplainableCrypto.Helios.Computational.ElectionDDHSourceCost
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-! Honest rejection in the actual public-input DDH games. The two-game
advantage is explicit; no rejection bound is transferred without it. -/
namespace ExplainableCrypto.Helios.Computational.ElectionDDHSource
open OracleComp OracleSpec ElectionOracle ElectionCache
open ElectionProgrammedSource (State evaluate evaluate_bind)
variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Return the publicly observed honest-rejection bit after the actual prefix.
The four DDH inputs are g, pk, A, T; neither a secret nor extraction is used. -/
def honestRejectDistinguisher {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    DiffieHellman.DDHAdversary F G := fun g pk A T =>
  (fun out => decide (out.1.1.before.honestDecisions ≠ (.accepted,.accepted))) <$>
    runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅

private abbrev FinalOutput (F G : Type) :=
  ((PublicResult F G × Bool) × State F G) × BallotOracleCache F G

private abbrev Rejected (out : FinalOutput F G) : Prop :=
  out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted)

omit [Fintype F] [DecidableEq F] in
private theorem finish_rejection {Saved : Type} (g pk : G) (secret : F)
    (adversary : Adversary F G Saved) (vote : Bool) (before : PublicPrefix F G)
    (submission : Ballot F G 2) (saved : Saved) (cast : Decision × List (BoardEntry F G))
    (s : State F G) (live : BallotOracleCache F G) :
    Pr[Rejected | evaluate (finishAfterCast g pk secret adversary vote before submission saved cast) s live] =
      if before.honestDecisions ≠ (.accepted,.accepted) then 1 else 0 := by
  have h := probEvent_congr' (p := Rejected) (q := fun _ => before.honestDecisions ≠ (.accepted,.accepted))
    (fun out ho => by
      have he := (finishAfterCast_publication g pk secret adversary vote before submission saved cast s live out ho).1
      simp only [Rejected,he]) rfl
  simpa only [probEvent_const,probFailure_eq_zero,tsub_zero] using h

omit [Fintype F] in
private theorem completed_rejection {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (secret : F) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Pr[Rejected | evaluate (completedReal fingerprint g pk A T secret prepare adversary) .empty ∅] =
      Pr[fun out => out.1.1.before.honestDecisions ≠ (.accepted,.accepted) |
        runBallotOracle (prefixSource fingerprint g pk A T prepare adversary) ∅] := by
  simp only [completedReal,evaluate_bind]
  rw [probEvent_bind_eq_tsum]
  conv_rhs => rw [probEvent_eq_tsum_ite]
  apply tsum_congr
  intro out
  rw [finish_rejection]
  by_cases h : out.1.1.before.honestDecisions ≠ (.accepted,.accepted) <;>
    simp [h,ElectionProgrammedSource.evaluate,prefixSource]

omit [Fintype F] in
/-- The actual pinned real DDH experiment has exactly the honest-rejection
probability of the complete real-challenge comparison. Later guessing is kept
in that comparison; it cannot change the recorded honest decisions. -/
theorem honestReject_real {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Pr[= true | DiffieHellman.ddhExpReal g (honestRejectDistinguisher fingerprint prepare adversary)] =
      Pr[fun out => out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted) |
        realGame fingerprint g prepare adversary] := by
  simp only [DiffieHellman.ddhExpReal,realGame,probOutput_bind_eq_tsum,probEvent_bind_eq_tsum]
  apply tsum_congr
  intro secret
  congr 1
  apply tsum_congr
  intro x
  congr 1
  rw [honestRejectDistinguisher,probOutput_map]
  simp only [decide_eq_true_eq]
  have he := completed_rejection fingerprint g (secret • g) (x • g) (x • (secret • g)) secret prepare adversary
  simpa only [smul_smul,mul_comm x secret,Rejected] using he.symm

/-- Derive real-world rejection from the historical complete game, including
the nonzero-key/four-nonce comparison loss and all prior proof-hash queries. -/
theorem honestReject_real_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c) :
    Pr[= true | DiffieHellman.ddhExpReal g (honestRejectDistinguisher fingerprint prepare adversary)] ≤
      9*noncePointBound F + ENNReal.ofReal ((11*(p : ℝ)+2*c+131)/(Fintype.card F : ℝ)) := by
  classical
  let actual := (fun out => ((out.1,false),out.2)) <$>
    run (ElectionExtraction.preparedSource fingerprint g prepare adversary) ∅
  let simulated := ElectionProgrammedSource.result <$> realGame fingerprint g prepare adversary
  let rejected : ElectionFullSimulation.Output F G → Bool :=
    fun out => decide (out.1.1.1.beforeTally.honestDecisions ≠ (.accepted,.accepted))
  have hd := prepared_real_distance_le fingerprint g hg prepare adversary p c hp hc
  have he := (abs_probOutput_toReal_sub_le_tvDist (rejected <$> actual) (rejected <$> simulated)).trans
    ((tvDist_map_le rejected actual simulated).trans hd)
  simp only [probOutput_map] at he
  have hr : Pr[fun out => rejected out = true | simulated].toReal ≤
      Pr[fun out => rejected out = true | actual].toReal +
        (11*(p : ℝ)+2*c+131)/(Fintype.card F : ℝ) := by linarith [(abs_le.mp he).1]
  have hb := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity),
    ENNReal.ofReal_toReal probEvent_ne_top,ENNReal.ofReal_toReal probEvent_ne_top] at hb
  have ha : Pr[fun out => rejected out = true | actual] ≤ 9*noncePointBound F := by
    simpa only [actual,rejected,probEvent_map,Function.comp_def,decide_eq_true_eq] using
      ElectionProgrammedExtraction.original_prepared_rejection_le fingerprint g hg prepare adversary
  rw [honestReject_real]
  simpa only [simulated,rejected,ElectionProgrammedSource.result,probEvent_map,Function.comp_def,
    decide_eq_true_eq] using hb.trans (add_le_add ha le_rfl)

omit [Fintype F] in
/-- Random-world rejection is charged to the real event plus this actual
public distinguisher's two-game DDH advantage. No hardness premise is hidden. -/
theorem honestReject_random_transfer {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) :
    Pr[= true | DiffieHellman.ddhExpRand g (honestRejectDistinguisher fingerprint prepare adversary)] ≤
      Pr[= true | DiffieHellman.ddhExpReal g (honestRejectDistinguisher fingerprint prepare adversary)] +
      ENNReal.ofReal (DiffieHellman.ddhDistAdvantage g (honestRejectDistinguisher fingerprint prepare adversary)) := by
  let d := honestRejectDistinguisher fingerprint prepare adversary
  have hr : (Pr[= true | DiffieHellman.ddhExpRand g d]).toReal ≤
      (Pr[= true | DiffieHellman.ddhExpReal g d]).toReal + DiffieHellman.ddhDistAdvantage g d := by
    unfold DiffieHellman.ddhDistAdvantage
    linarith [neg_abs_le ((Pr[= true | DiffieHellman.ddhExpReal g d]).toReal -
      (Pr[= true | DiffieHellman.ddhExpRand g d]).toReal)]
  have h := ENNReal.ofReal_le_ofReal hr
  have hn : 0 ≤ DiffieHellman.ddhDistAdvantage g d := abs_nonneg _
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hn,
    ENNReal.ofReal_toReal probOutput_ne_top,ENNReal.ofReal_toReal probOutput_ne_top] at h
  exact h

/-- The complete random-world rejection allowance, with historical collisions,
real-source simulation/sampling loss and the named DDH advantage all explicit. -/
theorem honestReject_random_le {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g))
    (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved) (p c : Nat)
    (hp : prepare.IsQueryBoundP (ElectionCacheBudget.isHash (F := F)) p)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsQueryBoundP
      (ElectionCacheBudget.isHash (F := F)) c) :
    Pr[= true | DiffieHellman.ddhExpRand g (honestRejectDistinguisher fingerprint prepare adversary)] ≤
      (9*noncePointBound F + ENNReal.ofReal ((11*(p : ℝ)+2*c+131)/(Fintype.card F : ℝ))) +
      ENNReal.ofReal (DiffieHellman.ddhDistAdvantage g (honestRejectDistinguisher fingerprint prepare adversary)) :=
  (honestReject_random_transfer fingerprint g prepare adversary).trans
    (add_le_add (honestReject_real_le fingerprint g hg prepare adversary p c hp hc) le_rfl)

/-- The public rejection experiment uses the derived actual prefix budget and
does not run extraction or guessing. Pure work remains outside this bound. -/
theorem honestReject_total_bound {Init Saved : Type} (fingerprint : PublicParameters F G → Nat)
    (g pk A T : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G Saved)
    (P C : Nat) (hs : (uniformSample F).IsTotalQueryBound 1) (hp : prepare.IsTotalQueryBound P)
    (hc : ∀ initial before, ((adversary initial).castBallot before).IsTotalQueryBound C) :
    (honestRejectDistinguisher fingerprint prepare adversary g pk A T).IsTotalQueryBound (4*P+4*C+78) := by
  apply (isQueryBound_map_iff _ _ _ _ _).mpr
  exact ballot_runtime_total_bound _ _ hs
    (prefix_total_bound fingerprint g pk A T prepare adversary P C hs hp hc) ∅

#print axioms honestReject_real
#print axioms honestReject_real_le
#print axioms honestReject_random_transfer
#print axioms honestReject_random_le
#print axioms honestReject_total_bound
end ExplainableCrypto.Helios.Computational.ElectionDDHSource
