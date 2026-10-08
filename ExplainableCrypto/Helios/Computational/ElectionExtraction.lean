import ExplainableCrypto.Helios.Computational.ElectionReplaySource
import ExplainableCrypto.Helios.Computational.RepairedSubmissionSource
import ExplainableCrypto.Helios.Computational.BallotWitnessConsistency

/-! Extract witnesses for the submission in the actual full election source.
The retained public record is the one passed to the guessing continuation.
These are conditional-success results. ElectionExtractionBound supplies the
real-source acceptance/replay bound; programmed honest-proof simulation remains open. -/
namespace ExplainableCrypto.Helios.Computational.ElectionExtraction
open OracleComp OracleSpec ElectionOracle ElectionCache
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [Fintype F]

/-- Instrument the original world with its actual public result, leaving all
private coins local and executing the complete guessing continuation. -/
noncomputable def worldSource {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (adversary : Adversary F G State) (vote : Bool) :
    Comp F G (PublicResult F G × Bool) := do
  let initial ← samplePrefix fingerprint g vote
  let (submission,saved) ← adversary.castBallot initial.2.2
  let view ← finishWithCoins initial.1 ![initial.2.1.1,initial.2.1.2] initial.2.2 submission
  let guess ← adversary.guessVote saved view
  pure (view,guess)

/-- Erasing the instrumentation gives exactly the original query computation. -/
theorem worldSource_project {State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (adversary : Adversary F G State) (vote : Bool) :
    Prod.snd <$> worldSource fingerprint g adversary vote = world fingerprint g adversary vote := by
  rw [world_eq_samplePrefix]
  simp [worldSource,map_eq_bind_pure_comp]

/-- Preparation and its oracle queries precede all original election sampling. -/
noncomputable def preparedSource {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) :
    Comp F G (PublicResult F G × Bool) := do
  let initial ← prepare
  let vote ← liftProb (uniformSample Bool)
  let (view,guess) ← worldSource fingerprint g (adversary initial) vote
  pure (view,decide (guess = vote))

theorem preparedSource_project {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) :
    Prod.snd <$> preparedSource fingerprint g prepare adversary =
      preparedGame fingerprint g prepare adversary := by
  simp only [preparedSource,preparedGame,game,map_bind,map_pure]
  apply bind_congr
  intro initial
  apply bind_congr
  intro vote
  rw [← worldSource_project fingerprint g (adversary initial) vote,bind_map_left]

/-- Rejected records select a proof with an impossible first branch when g ≠ 0. -/
def select (g : G) (i : Option (Fin 2)) (out : PublicResult F G × Bool) :
    BallotStatement G × Proof01 F G :=
  (out.1.submission.coveredStatement g out.1.beforeTally.parameters.publicKey i,
    if out.1.decision = .accepted then out.1.submission.coveredProof i else replayRejectedProof g)

variable [SampleableType F]

noncomputable def joint {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (prepare : Comp F G Init) (adversary : Init → Adversary F G State) (n : Nat) :=
  ElectionReplaySource.jointExtract (preparedSource fingerprint g prepare adversary) (select g) n

/-- All three witnesses concern the same actual accepted submission, with its
actual public key, in a supported complete election execution. -/
theorem joint_valid {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : g ≠ 0) (prepare : Comp F G Init)
    (adversary : Init → Adversary F G State) (n : Nat)
    (out : PublicResult F G × Bool) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (joint fingerprint g prepare adversary n)) :
    out.1.decision = .accepted ∧
      (∀ i, (out.1.submission.coveredStatement g out.1.beforeTally.parameters.publicKey i).Witnesses (w i)) ∧
      ∃ cache, (out,cache) ∈ support
        (run (preparedSource fingerprint g prepare adversary) (fun _ => none)) := by
  obtain ⟨hv,hsource⟩ := ElectionReplaySource.jointExtract_valid _ _ n out w ho
  have ha : out.1.decision = .accepted := by
    by_contra hn
    obtain ⟨c,hproof⟩ := (hv none).2
    simp only [select,if_neg hn,Ballot.coveredStatement] at hproof
    exact hg (by simpa [replayRejectedProof,Branch.Valid] using hproof.1.1.symm)
  exact ⟨ha,fun i => (hv i).1,hsource⟩

/-- The algorithmically produced component/aggregate witnesses have consistent
nonces and integer at-most-one votes; characteristic two is explicitly excluded. -/
theorem joint_consistent {Init State : Type} (fingerprint : PublicParameters F G → Nat)
    (g : G) (hg : Function.Injective (fun r : F => r • g)) (h2 : (2 : F) ≠ 0)
    (prepare : Comp F G Init) (adversary : Init → Adversary F G State) (n : Nat)
    (out : PublicResult F G × Bool) (w : Option (Fin 2) → BallotWitness F)
    (ho : some (out,w) ∈ support (joint fingerprint g prepare adversary n)) :
    out.1.decision = .accepted ∧ (w none).2 = (w (some 0)).2 + (w (some 1)).2 ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat = (w none).1.toNat ∧
      (w (some 0)).1.toNat + (w (some 1)).1.toNat ≤ 1 := by
  have hg0 : g ≠ 0 := by
    intro he
    exact one_ne_zero (hg (by simp [he]) : (1 : F) = 0)
  obtain ⟨ha,hw,_⟩ := joint_valid fingerprint g hg0 prepare adversary n out w ho
  exact ⟨ha,(out.1.submission.covered_witnesses_sum g _ hg w hw).1,
    out.1.submission.covered_witnesses_atMostOne g _ hg h2 w hw⟩

#print axioms worldSource_project
#print axioms preparedSource_project
#print axioms joint_valid
#print axioms joint_consistent
end ExplainableCrypto.Helios.Computational.ElectionExtraction
