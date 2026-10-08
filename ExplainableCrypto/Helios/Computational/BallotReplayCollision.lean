import ExplainableCrypto.Helios.Computational.BallotReplayMass

/-! A conditional second completion loses at most one uniform challenge point.
The probability refers to the actual rich ballot replay, including its original
full-proof selector and equal-challenge rejection. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
attribute [local implicit_reducible] ballotForkBudget
variable {F G A : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F] [Fintype F]
local instance replayCollisionInhabited : Inhabited F := ⟨0⟩
noncomputable local instance replayCollisionUniform : IsUniformSpec ((Unit →ₒ F) : OracleSpec _) :=
  IsUniformSpec.ofFintypeInhabited _

/-- At a selected original path, conditional replay retains the selected-event
mass except for at most one fresh uniform challenge point. -/
theorem ballotReplayAtPath_mass_le
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace oa)) (s : Fin (n+1))
    (hs : ballotForkSelector n (PFunctor.FreeM.output _ path) = some s) :
    ballotReplayContextMass (ballotForkRunTrace oa) (.inr ()) s
        (fun x => ballotForkSelector n x = some s) path - (Fintype.card F : ENNReal)⁻¹ ≤
      Pr[fun out => out.isSome | ballotReplayAtPath oa n path] := by
  have hr := CfReachable.toPathCfReachable (ballotFork_selector_reachable oa n) path s hs
  cases hl : PFunctor.FreeM.Cursor.locateAt?
      (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor) (Sum.inr ())
      (ballotForkRunTrace oa) path s with
  | none => simp [hl] at hr
  | some located =>
    have hfirst : ballotForkSelector n (PFunctor.FreeM.output _ located.completion.path) = some s := by
      rwa [located.path_eq]
    have hevent : Pr[fun out => out.isSome | ballotReplayAtPath oa n path] =
        Pr[fun second => located.completion.answer ≠ second.answer ∧
          ballotForkSelector n (PFunctor.FreeM.output _ second.path) = some s |
          Cursor.completeOccurrence located.occurrence] := by
      unfold ballotReplayAtPath
      rw [hs]
      dsimp only
      rw [hl]
      dsimp only
      rw [probEvent_map]
      apply probEvent_congr' _ rfl
      intro second _
      by_cases hne : located.completion.answer = second.answer <;>
        by_cases hcf : ballotForkSelector n (PFunctor.FreeM.output _ second.path) = some s <;>
        simp [acceptContextForkWitness,classifyForkView,hfirst,hne,hcf]
    rw [hevent]
    unfold ballotReplayContextMass
    rw [hl]
    have hcollision : Pr[fun second => located.completion.answer = second.answer |
        Cursor.completeOccurrence located.occurrence] ≤ (Fintype.card F : ENNReal)⁻¹ := by
      apply (probEvent_answer_ofFreeM_complete (spec := FiatShamir.Fork.wrappedSpec F) located.occurrence
        (fun answer => located.completion.answer = answer)).trans_le
      exact probEvent_query_le_inv_of_unique (spec := FiatShamir.Fork.wrappedSpec F) (.inr ()) _ (fun x y hx hy => hx.symm.trans hy)
    apply tsub_le_iff_right.mpr
    apply le_trans ?_ (add_le_add le_rfl hcollision)
    apply probEvent_le_add_of_imp_or
    intro second _ hselect
    by_cases he : located.completion.answer = second.answer
    · exact Or.inr he
    · exact Or.inl ⟨he,hselect⟩

/-- A selected shared-source path outside the low-mass event has this actual
conditional witness-extraction probability. -/
theorem ballotReplaySourceAttempt_threshold_le (oa : BallotOracleComp F G A)
    (select : A → BallotStatement G × Proof01 F G) (n : Nat) (δ : ENNReal)
    (path : PFunctor.FreeM.Path (ballotReplaySourceRun oa))
    (hs : (ballotForkSelector n (PFunctor.FreeM.output _
      (ballotReplaySourcePath oa select path))).isSome)
    (hgood : ¬ ballotReplayBadContext (select <$> oa) n δ (ballotReplaySourcePath oa select path)) :
    δ - (Fintype.card F : ENNReal)⁻¹ ≤ Pr[fun out => out.isSome |
      ballotReplaySourceAttempt oa select n path] := by
  rw [ballotReplaySourceAttempt,probEvent_map]
  simp only [Function.comp_def,Option.isSome_map]
  cases he : ballotForkSelector n (PFunctor.FreeM.output _ (ballotReplaySourcePath oa select path)) with
  | none => simp [he] at hs
  | some s =>
    have hmass : δ ≤ ballotReplayContextMass (ballotForkRunTrace (select <$> oa)) (.inr ()) s
        (fun x => ballotForkSelector n x = some s) (ballotReplaySourcePath oa select path) := by
      apply le_of_lt
      apply lt_of_not_ge
      intro hm
      exact hgood ⟨s,he,hm⟩
    exact (tsub_le_tsub_right hmass _).trans (ballotReplayAtPath_mass_le _ n _ s he)

#print axioms ballotReplayAtPath_mass_le
#print axioms ballotReplaySourceAttempt_threshold_le
end ExplainableCrypto.Helios.Computational
