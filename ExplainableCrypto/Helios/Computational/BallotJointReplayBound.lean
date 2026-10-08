import ExplainableCrypto.Helios.Computational.BallotReplayCollision
import ExplainableCrypto.Helios.Computational.BallotJointReplay

/-! A common-path probability argument for the actual three replay attempts.
Low-success contexts are charged on one shared original execution; second
completions remain independent conditional on that path by the program's binds. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
local instance jointBoundInhabited : Inhabited F := ⟨0⟩
noncomputable local instance jointBoundUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

def ballotJointReplayBadContext (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) : Prop :=
  ∃ i : Option (Fin 2), ballotReplayBadContext (select i <$> oa) n δ
    (ballotReplaySourcePath oa (select i) path)

/-- The low-context loss for all three selections is charged on the same
original path distribution, not on independent first executions. -/
theorem ballotJointReplay_bad_context_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal) :
    Pr[ballotJointReplayBadContext oa select n δ | replayFirstPath (ballotReplaySourceRun oa)] ≤
      3 * (n+1 : ENNReal) * δ := by
  classical
  unfold ballotJointReplayBadContext
  calc
    _ ≤ ∑ i : Option (Fin 2), Pr[fun path => ballotReplayBadContext (select i <$> oa) n δ
        (ballotReplaySourcePath oa (select i) path) | replayFirstPath (ballotReplaySourceRun oa)] := by
      simpa only [Finset.mem_univ,true_and] using probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Option (Fin 2))) (replayFirstPath (ballotReplaySourceRun oa))
        (fun i path => ballotReplayBadContext (select i <$> oa) n δ
          (ballotReplaySourcePath oa (select i) path))
    _ ≤ ∑ _ : Option (Fin 2), (n+1 : ENNReal)*δ :=
      Finset.sum_le_sum (fun i _ => ballotReplay_bad_source_context_le oa (select i) n δ)
    _ = _ := by simp [mul_assoc]

/-- Three fixed-path attempts with individual success at least ε succeed
together with probability at least ε³. This follows from the actual binds. -/
theorem ballotJointReplayAtPath_product_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) (ε : ENNReal)
    (h : ∀ i, ε ≤ Pr[fun out => out.isSome | ballotReplaySourceAttempt oa (select i) n path]) :
    ε^3 ≤ Pr[fun out => out.isSome | ballotJointReplayAtPath oa select n path] := by
  unfold ballotJointReplayAtPath
  rw [show ε^3 = ε*(ε*ε) by ring]
  apply mul_le_probEvent_bind (h (some 0))
  intro w0 _ hw0
  cases w0 with
  | none => simp at hw0
  | some w0 =>
    apply mul_le_probEvent_bind (h (some 1))
    intro w1 _ hw1
    cases w1 with
    | none => simp at hw1
    | some w1 =>
      apply (h none).trans_eq
      rw [bind_pure_comp,probEvent_map]
      apply probEvent_congr' _ rfl
      intro wa _
      cases wa <;> rfl

/-- Outside the low-context event, enabled original selectors yield the actual
joint conditional replay lower bound, retaining equal-challenge failures. -/
theorem ballotJointReplayAtPath_threshold_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa))
    (hs : ∀ i, (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa (select i) path))).isSome)
    (hg : ¬ ballotJointReplayBadContext oa select n δ path) :
    (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | ballotJointReplayAtPath oa select n path] := by
  apply ballotJointReplayAtPath_product_le
  intro i
  exact ballotReplaySourceAttempt_threshold_le oa (select i) n δ path (hs i)
    (fun hi => hg ⟨i,hi⟩)

/-- General bound for this concrete three-attempt construction. Its initial
event is simultaneous original selection, which actual submission coverage
identifies with joint acceptance in the protocol. -/
theorem ballotJointReplay_selection_le (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal) :
    let α := Pr[fun path => ∀ i, (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa (select i) path))).isSome | replayFirstPath (ballotReplaySourceRun oa)]
    (α - 3*(n+1 : ENNReal)*δ) * (δ - (Fintype.card F : ENNReal)⁻¹)^3 ≤
      Pr[fun out => out.isSome | ballotJointReplay oa select n] := by
  classical
  let enabled := fun path : PFunctor.FreeM.Path (ballotReplaySourceRun oa) =>
    ∀ i, (ballotForkSelector n (PFunctor.FreeM.output _ (ballotReplaySourcePath oa (select i) path))).isSome
  let good := fun path => enabled path ∧ ¬ ballotJointReplayBadContext oa select n δ path
  have hgood : Pr[enabled | replayFirstPath (ballotReplaySourceRun oa)] - 3*(n+1 : ENNReal)*δ ≤
      Pr[good | replayFirstPath (ballotReplaySourceRun oa)] := by
    apply tsub_le_iff_right.mpr
    apply le_trans ?_ (add_le_add le_rfl (ballotJointReplay_bad_context_le oa select n δ))
    apply probEvent_le_add_of_imp_or
    intro path _ hs
    by_cases hb : ballotJointReplayBadContext oa select n δ path
    · exact Or.inr hb
    · exact Or.inl ⟨hs,hb⟩
  unfold ballotJointReplay
  apply mul_le_probEvent_bind hgood
  intro path _ hg
  rw [probEvent_map]
  simp only [Function.comp_def,Option.isSome_map]
  exact ballotJointReplayAtPath_threshold_le oa select n δ path hg.1 hg.2

/-- The actual source output determines each selector pointwise. This is used
both for acceptance mass and for failure on one retained original execution. -/
theorem ballotJointReplay_selector_eq (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G)
    (n : Nat) (accepted : A → Prop) [DecidablePred accepted]
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (hv : ∀ raw : A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F,
      (raw.1,ballotForkCacheProject raw.2.1) ∈ support (runBallotOracle oa ∅) →
      ∀ i, (ballotForkSourceTrace (select i) raw).verified = decide (accepted raw.1))
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa)) (i : Option (Fin 2)) :
    (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa (select i) path))).isSome =
      decide (accepted (PFunctor.FreeM.output _ path).1) := by
  have hbudget : (select i <$> oa).IsQueryBoundP (isBallotHashQuery (F := F)) (n+1) := by
    rw [isQueryBoundP_map_iff]
    exact hb.mono (by omega)
  have supportedOutput {ι : Type} {spec : OracleSpec.{0,0} ι} {B : Type}
      (m : OracleComp spec B) (p : PFunctor.FreeM.Path m) :
      PFunctor.FreeM.output m p ∈ support m := by
    have hp : PFunctor.FreeM.output m p ∈ support (PFunctor.FreeM.output m <$> replayFirstPath m) := by
      rw [support_map]
      exact Set.mem_image_of_mem _ (mem_support_replayFirstPath m p)
    rwa [map_output_replayFirstPath] at hp
  rw [ballotFork_selector_of_bound _ n hbudget _ (supportedOutput _ _)]
  exact (congrArg (fun t : BallotForkTrace F G => t.verified)
    (ballotReplaySourcePath_output oa (select i) path)).trans
      (hv _ (ballotReplaySourcePath_runtime_mem oa path) i)

/-- Shared source-selection correspondence used by both complete elections and
submission prefixes. The caller proves the verification predicate for every
actual supported source output; output-law equality alone does not supply it. -/
theorem ballotJointReplay_selection_probability (oa : BallotOracleComp F G A)
    (select : Option (Fin 2) → A → BallotStatement G × Proof01 F G)
    (n : Nat) (accepted : A → Prop) [DecidablePred accepted]
    (hb : oa.IsQueryBoundP (isBallotHashQuery (F := F)) n)
    (hv : ∀ raw : A × FiatShamir.Fork.SimState Unit (BallotForkPoint G) F,
      (raw.1,ballotForkCacheProject raw.2.1) ∈ support (runBallotOracle oa ∅) →
      ∀ i, (ballotForkSourceTrace (select i) raw).verified = decide (accepted raw.1)) :
    Pr[fun path => ∀ i : Option (Fin 2), (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa (select i) path))).isSome |
      replayFirstPath (ballotReplaySourceRun oa)] =
    Pr[fun out => accepted out.1 | runBallotOracle oa ∅] := by
  have path_selector := ballotJointReplay_selector_eq oa select n accepted hb hv
  have hsource : Pr[fun raw => accepted raw.1 | ballotReplaySourceRun oa] =
      Pr[fun out => accepted out.1 | runBallotOracle oa ∅] := by
    calc
      _ = Pr[fun raw => accepted raw.1 | simulateQ ballotForkEntropyImpl (ballotReplaySourceRun oa)] :=
        (probEvent_congr' (fun _ _ => Iff.rfl) (ballotFork_entropy_eval _)).symm
      _ = _ := by
        have h := congrArg (fun m => Pr[fun out => accepted out.1 | m]) (ballotFork_runtime_eq oa (∅,[]))
        have he : ballotForkCacheProject (∅ : (Unit × BallotForkPoint G →ₒ F).QueryCache) =
            (∅ : BallotOracleCache F G) := by funext key; rfl
        simpa only [he,probEvent_map,Function.comp_def,Prod.map,id_eq,ballotReplaySourceRun] using h
  calc
    _ = Pr[fun path => accepted (PFunctor.FreeM.output _ path).1 |
        replayFirstPath (ballotReplaySourceRun oa)] := by
      apply probEvent_congr' _ rfl
      intro path _
      simp only [path_selector,decide_eq_true_eq,forall_const]
    _ = Pr[fun raw => accepted raw.1 | ballotReplaySourceRun oa] := by
      have h := congrArg (fun m => Pr[fun raw => accepted raw.1 | m]) (map_output_replayFirstPath (ballotReplaySourceRun oa))
      simpa only [probEvent_map,Function.comp_def] using h
    _ = _ := hsource

#print axioms ballotJointReplay_selector_eq
#print axioms ballotJointReplay_selection_probability
#print axioms ballotJointReplay_bad_context_le
#print axioms ballotJointReplayAtPath_product_le
#print axioms ballotJointReplayAtPath_threshold_le
#print axioms ballotJointReplay_selection_le
end ExplainableCrypto.Helios.Computational
