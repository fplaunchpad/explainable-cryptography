import ExplainableCrypto.Helios.Symbolic.SourceLocalNormalization
import ExplainableCrypto.Helios.Symbolic.SourceFrameSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Finite provider application leaves variables outside its explicit domain
unchanged. In particular, a newly captured public variable stays a variable. -/
theorem entriesSubst_outside (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    (v : V) (hv : ∀ i, v ≠ vars i) : entriesSubst h vars values v = .var v := by
  classical
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [entriesSubst,replaceVar,if_neg (hv (Fin.last h)),Term.subst]
    exact ih _ _ (fun i => hv i.castSucc)

/-- Retain an unrelated frame while one provider substitutes into an arbitrary
context, including active payloads and local binders. -/
theorem substExtended_beside_context (x : V) (m : Term V) (f a : Extended V)
    (ha : ¬ a.Exports x) :
    Structural (.par (.par (.active x m) f) a)
      (.par (.par (.active x m) f) (a.substFree x m)) := by
  have rearrange (b : Extended V) :
      Structural (.par (.par (.active x m) f) b) (.par f (.par (.active x m) b)) :=
    (Structural.parLeft _ (Structural.comm _ _)).trans (Structural.assoc _ _ _)
  exact (rearrange a).trans
    ((Structural.parRight f (Structural.substExtended x m a ha)).trans (rearrange _).symm)

/-- All finite ground providers instantiate the same entire context. Exact
syntax, the provider frame and an original structural path are retained. -/
theorem frameEntries_apply_extended (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    (a : Extended V) (ha : ∀ i, ¬ a.Exports (vars i)) :
    ∃ b, Instantiates (entriesSubst h vars values) a b ∧
      Structural (.par (frameEntries h vars values) a) (.par (frameEntries h vars values) b) := by
  induction h generalizing a with
  | zero =>
    refine ⟨a,?_,.refl _⟩
    simpa only [entriesSubst,rename_id,id_eq] using instantiates_rename a id
  | succ h ih =>
    let x := vars (Fin.last h)
    let m : Term V := groundTerm (values (Fin.last h))
    have hs := substExtended_beside_context x m
      (frameEntries h (fun i => vars i.castSucc) (fun i => values i.castSucc)) a (ha (Fin.last h))
    obtain ⟨b,hb,hj⟩ := ih (fun i => vars i.castSucc) (fun i => values i.castSucc) (a.substFree x m)
      (fun i he => ha i.castSucc ((substFree_exports a x m (vars i.castSucc)).mp he))
    have hg := (instantiates_substFree a x m (ha (Fin.last h))).comp hb
    refine ⟨b,hg,?_⟩
    exact hs.trans ((Structural.assoc _ _ _).trans ((Structural.parRight _ hj).trans (Structural.assoc _ _ _).symm))

/-- A supplied exact instantiation identifies the whole target uniquely. -/
theorem frameEntries_apply_instantiates (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    {a b : Extended V} (ha : ∀ i, ¬ a.Exports (vars i))
    (hb : Instantiates (entriesSubst h vars values) a b) :
    Structural (.par (frameEntries h vars values) a) (.par (frameEntries h vars values) b) := by
  obtain ⟨c,hc,hs⟩ := frameEntries_apply_extended h vars values a ha
  exact (hc.unique hb) ▸ hs

/-- Full old-handle substitution under a fresh variable leaves that new None
untouched and grounds every old Some using its own complete frame value. -/
theorem entriesSubst_shifted_frame (φ : Frame restricted handles) :
    entriesSubst handles (some : Fin handles → Option (Fin handles)) φ.value =
      liftSubst (fun i => groundTerm (φ.value i)) := by
  funext v
  cases v with
  | none => exact entriesSubst_outside _ _ _ none (by simp)
  | some i =>
    rw [entriesSubst_value _ _ _ (Option.some_injective _) i]
    exact (groundTerm_rename _ some).symm

/-- Ground the old public variables in an arbitrary fresh-handle context.
The context may retain local binders and export the new None. -/
theorem shiftedFrame_apply_instantiates (φ : Frame restricted handles)
    {a b : Extended (Option (Fin handles))} (ha : ∀ i, ¬ a.Exports (some i))
    (hb : Instantiates (liftSubst (fun i => groundTerm (φ.value i))) a b) :
    Structural (.par ((activeFrame φ).rename some) a)
      (.par ((activeFrame φ).rename some) b) := by
  have hg : Instantiates (entriesSubst handles some φ.value) a b := by
    simpa only [entriesSubst_shifted_frame] using hb
  simpa only [activeFrame,frameEntries_rename,Function.comp_id] using
    frameEntries_apply_instantiates handles some φ.value ha hg

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
