import ExplainableCrypto.Helios.Computational.BallotForkSource

/-! Conditional replay at an already sampled first path. This is the existing
VCVio rich fork with its initial execution factored out, for shared-ballot replay. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
attribute [local implicit_reducible] ballotForkBudget
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G] [SampleableType F]

def ballotReplayAtPath
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace oa)) :
    OracleComp (FiatShamir.Fork.wrappedSpec F)
      (Option (ContextForkWitness (ballotForkRunTrace oa) (ballotForkBudget (F := F) n) (.inr ()))) :=
  match ballotForkSelector n (PFunctor.FreeM.output _ path) with
  | none => pure none
  | some s =>
    match PFunctor.FreeM.Cursor.locateAt? (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor) (Sum.inr ()) (ballotForkRunTrace oa) path s with
    | none => pure none
    | some located =>
      (fun second => acceptContextForkWitness (ballotForkRunTrace oa)
        (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n) s
        { occurrence := located.occurrence, first := located.completion, second := second }) <$>
        Cursor.completeOccurrence located.occurrence

/-- Sampling the first path once and attempting replay is exactly the existing
rich fork computation. No distributional correspondence is assumed. -/
theorem ballotReplayAtPath_bind
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat) :
    (do let path ← replayFirstPath (ballotForkRunTrace oa)
        ballotReplayAtPath oa n path) =
      contextForkWitness (ballotForkRunTrace oa) (ballotForkBudget (F := F) n)
        (.inr ()) (ballotForkSelector n) := by
  unfold contextForkWitness
  rw [PFunctor.FreeM.Cursor.filterMapLocateAndForkSelected_eq_filterMapLocateAndForkBy,
    PFunctor.FreeM.Cursor.filterMapLocateAndForkBy_eq_bind_complete]
  change _ = (replayFirstPath (ballotForkRunTrace oa) >>= _)
  apply bind_congr
  intro path
  unfold ballotReplayAtPath
  rcases hs : ballotForkSelector n (PFunctor.FreeM.output _ path) with _ | s
  · simp only
  · simp only
    rcases hl : PFunctor.FreeM.Cursor.locateAt?
      (P := (FiatShamir.Fork.wrappedSpec F).toPFunctor) (Sum.inr ())
      (ballotForkRunTrace oa) path s with _ | located
    · simp only
    · simp only
      rfl

/-- A supported conditional completion is a supported existing rich fork. -/
theorem ballotReplayAtPath_supported
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace oa))
    (w : ContextForkWitness (ballotForkRunTrace oa) (ballotForkBudget (F := F) n) (.inr ()))
    (hw : some w ∈ support (ballotReplayAtPath oa n path)) :
    some w ∈ support (contextForkWitness (ballotForkRunTrace oa)
      (ballotForkBudget (F := F) n) (.inr ()) (ballotForkSelector n)) := by
  rw [← ballotReplayAtPath_bind,mem_support_bind_iff]
  exact ⟨path,mem_support_replayFirstPath _ path,hw⟩

/-- The first path is the supplied original execution, including all answers. -/
theorem ballotReplayAtPath_first
    (oa : BallotOracleComp F G (BallotStatement G × Proof01 F G)) (n : Nat)
    (path : PFunctor.FreeM.Path (ballotForkRunTrace oa))
    (w : ContextForkWitness (ballotForkRunTrace oa) (ballotForkBudget (F := F) n) (.inr ()))
    (hw : some w ∈ support (ballotReplayAtPath oa n path)) : w.view.firstPath = path := by
  unfold ballotReplayAtPath at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · rename_i s hs located hl
      rw [support_map] at hw
      obtain ⟨second,_,he⟩ := hw
      unfold acceptContextForkWitness at he
      dsimp only at he
      split at he
      · cases Option.some.inj he
        exact located.path_eq
      · simp at he

#print axioms ballotReplayAtPath_bind
#print axioms ballotReplayAtPath_supported
#print axioms ballotReplayAtPath_first
end ExplainableCrypto.Helios.Computational
