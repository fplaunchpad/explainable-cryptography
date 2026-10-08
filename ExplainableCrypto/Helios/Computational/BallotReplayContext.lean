import ExplainableCrypto.Helios.Computational.BallotReplayPath

/-! Conditional success at an actual stopped replay context. This is the
fixed-ordinal small-mass estimate needed for the joint ballot extractor, using
PolyFun's existing split/completion semantics. -/
namespace ExplainableCrypto.Helios.Computational
open OracleComp OracleSpec
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx
variable {ι α : Type} {spec : OracleSpec ι} [spec.DecidableEq] [IsUniformSpec spec]

noncomputable def ballotReplayContextMass (main : OracleComp spec α) (i : ι) (n : Nat)
    (event : α → Prop) (path : PFunctor.FreeM.Path main) : ENNReal :=
  match PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n with
  | none => 0
  | some located => Pr[fun completed => event (PFunctor.FreeM.output main completed.path) |
      Cursor.completeOccurrence located.occurrence]

/-- Every completion recovers the same stopped context, so its conditional
success mass is independent of which original completion was sampled. -/
theorem ballotReplayContextMass_completion (main : OracleComp spec α) (i : ι) (n : Nat)
    (event : α → Prop) (occ : PFunctor.FreeM.Cursor.Occurrence i main n)
    (completed : occ.Completion) :
    ballotReplayContextMass main i n event completed.path =
      Pr[fun other => event (PFunctor.FreeM.output main other.path) | Cursor.completeOccurrence occ] := by
  unfold ballotReplayContextMass
  rw [PFunctor.FreeM.Cursor.locateAt?_completion_path]
  rfl

private theorem bad_mass_complete_le (main : OracleComp spec α) (i : ι) (n : Nat)
    (event : α → Prop)
    (hreach : ∀ path : PFunctor.FreeM.Path main, event (PFunctor.FreeM.output main path) →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n).isSome)
    (δ : ENNReal) (split : PFunctor.FreeM.Cursor.Split i main n) (hvalid : split.Valid) :
    Pr[fun path => event (PFunctor.FreeM.output main path) ∧
      ballotReplayContextMass main i n event path ≤ δ | Cursor.complete split] ≤ δ := by
  classical
  let : DecidableEq spec.Domain := inferInstance
  cases split with
  | missing path =>
    have hno : ¬ event (PFunctor.FreeM.output main path) := by
      intro he
      exact Nat.not_lt_of_ge hvalid
        ((PFunctor.FreeM.Cursor.locateAt?_isSome_iff_lt_occurrences (P := spec.toPFunctor) i main path n).mp (hreach path he))
    change Pr[fun p => event (PFunctor.FreeM.output main p) ∧
      ballotReplayContextMass main i n event p ≤ δ | (pure path : OracleComp spec _)] ≤ δ
    simp [hno]
  | found occ =>
    change Pr[fun path => event (PFunctor.FreeM.output main path) ∧
      ballotReplayContextMass main i n event path ≤ δ |
      PFunctor.FreeM.Cursor.Occurrence.Completion.path <$> Cursor.completeOccurrence occ] ≤ δ
    rw [probEvent_map]
    simp only [Function.comp_def,ballotReplayContextMass_completion]
    by_cases h : Pr[fun completed => event (PFunctor.FreeM.output main completed.path) |
        Cursor.completeOccurrence occ] ≤ δ
    · simp only [h,and_true]
    · simp only [h,and_false,probEvent_False,zero_le]

/-- Selecting a fixed occurrence through a context of conditional success at
most δ has probability at most δ. Reachability is the only structural premise;
its ballot instance is derived from the checked raw selector. -/
theorem ballotReplay_bad_context_fixed_le (main : OracleComp spec α) (i : ι) (n : Nat)
    (event : α → Prop)
    (hreach : ∀ path : PFunctor.FreeM.Path main, event (PFunctor.FreeM.output main path) →
      (PFunctor.FreeM.Cursor.locateAt? (P := spec.toPFunctor) i main path n).isSome)
    (δ : ENNReal) :
    Pr[fun path => event (PFunctor.FreeM.output main path) ∧
      ballotReplayContextMass main i n event path ≤ δ | replayFirstPath main] ≤ δ := by
  have hsplit : (Cursor.splitAtValid main i n >>= fun certified => Cursor.complete certified.1) =
      replayFirstPath main := PFunctor.FreeM.Cursor.splitAtValid_bind_complete i main n
  rw [← hsplit]
  apply probEvent_bind_le_of_forall_le
  intro certified _
  exact bad_mass_complete_le main i n event hreach δ certified.1 certified.2

#print axioms ballotReplayContextMass_completion
#print axioms ballotReplay_bad_context_fixed_le
end ExplainableCrypto.Helios.Computational
