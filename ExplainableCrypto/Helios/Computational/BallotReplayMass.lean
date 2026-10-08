import ExplainableCrypto.Helios.Computational.BallotReplayContext
import ExplainableCrypto.Helios.Computational.BallotReplaySource

/-! Low conditional-success contexts for an actual raw ballot selector.
Occurrence reachability is derived, and pure source-path projection preserves
the bad-event distribution used by joint replay. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
attribute [local implicit_reducible] ballotForkBudget
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
local instance replayMassInhabited : Inhabited F := ⟨0⟩
noncomputable local instance replayMassUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

def ballotReplayBadContext (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G))
    (n : Nat) (δ : ENNReal) (path : PFunctor.FreeM.Path (ballotForkRunTrace oa)) : Prop :=
  ∃ s : Fin (n+1), ballotForkSelector n (PFunctor.FreeM.output _ path) = some s ∧
    ballotReplayContextMass (ballotForkRunTrace oa) (.inr ()) s
      (fun x => ballotForkSelector n x = some s) path ≤ δ

/-- The actual selector's reachability discharges the structural premise of
the fixed-context mass bound; no cache or query-occurrence assumption is added. -/
theorem ballotReplay_bad_context_index_le
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G))
    (n : Nat) (s : Fin (n+1)) (δ : ENNReal) :
    Pr[fun path => ballotForkSelector n (PFunctor.FreeM.output _ path) = some s ∧
      ballotReplayContextMass (ballotForkRunTrace oa) (.inr ()) s
        (fun x => ballotForkSelector n x = some s) path ≤ δ |
      replayFirstPath (ballotForkRunTrace oa)] ≤ δ := by
  exact ballotReplay_bad_context_fixed_le (spec := FiatShamir.Fork.wrappedSpec F)
    (ballotForkRunTrace oa) (.inr ()) (s : Nat) (fun x => ballotForkSelector n x = some s)
    (fun path hs => CfReachable.toPathCfReachable (ballotFork_selector_reachable oa n) path s hs) δ

/-- The probability of selecting any low-success context is at most the
selector-domain size times the threshold. -/
theorem ballotReplay_bad_context_le
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G))
    (n : Nat) (δ : ENNReal) :
    Pr[ballotReplayBadContext oa n δ | replayFirstPath (ballotForkRunTrace oa)] ≤
      (n+1 : ENNReal) * δ := by
  classical
  unfold ballotReplayBadContext
  calc
    _ ≤ ∑ s : Fin (n+1), Pr[fun path =>
        ballotForkSelector n (PFunctor.FreeM.output _ path) = some s ∧
        ballotReplayContextMass (ballotForkRunTrace oa) (.inr ()) s
          (fun x => ballotForkSelector n x = some s) path ≤ δ |
        replayFirstPath (ballotForkRunTrace oa)] := by
      simpa only [Finset.mem_univ,true_and] using
        probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin (n+1)))
          (replayFirstPath (ballotForkRunTrace oa)) (fun s path =>
            ballotForkSelector n (PFunctor.FreeM.output _ path) = some s ∧
            ballotReplayContextMass (ballotForkRunTrace oa) (.inr ()) s
              (fun x => ballotForkSelector n x = some s) path ≤ δ)
    _ ≤ ∑ _ : Fin (n+1), δ := Finset.sum_le_sum (fun s _ => ballotReplay_bad_context_index_le oa n s δ)
    _ = _ := by simp

/-- The same bound holds after pure projection of one shared original source
path. This is the distribution used by each attempt of the actual joint code. -/
theorem ballotReplay_bad_source_context_le (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal) :
    Pr[fun path => ballotReplayBadContext (select <$> oa) n δ
        (ballotReplaySourcePath oa select path) | replayFirstPath (ballotReplaySourceRun oa)] ≤
      (n+1 : ENNReal) * δ := by
  have h := ballotReplay_bad_context_le (select <$> oa) n δ
  rw [← ballotReplaySourcePath_distribution oa select,probEvent_map] at h
  exact h

#print axioms ballotReplay_bad_context_index_le
#print axioms ballotReplay_bad_context_le
#print axioms ballotReplay_bad_source_context_le
end ExplainableCrypto.Helios.Computational
