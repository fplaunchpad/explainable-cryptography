import ExplainableCrypto.Helios.Symbolic.SourceOutputDerivation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V W : Type} {restricted : Finset Nat} {handles : Nat}

/-- Ground payloads are fixed under arbitrary variable substitution. -/
theorem groundTerm_subst (m : Ground) (σ : V → Term W) :
    (groundTerm m).subst σ = groundTerm m := by
  simp only [groundTerm,Term.subst_subst]
  congr 1
  funext v
  exact v.elim

theorem groundAgent_subst (p : Agent Empty) (σ : V → Term W) :
    (groundAgent p).subst σ = groundAgent p := by
  simp only [groundAgent,Agent.subst_subst]
  congr 1
  funext v
  exact v.elim

/-- Sequential application of the explicit active bindings, newest first.
The result is a substitution on uses; the active domains are never replaced. -/
noncomputable def entriesSubst : (h : Nat) → (Fin h → V) → (Fin h → Ground) → V → Term V
  | 0, _, _ => Term.var
  | h+1, vars, values => fun v =>
      (replaceVar (vars (Fin.last h)) (groundTerm (values (Fin.last h))) v).subst
        (entriesSubst h (fun i => vars i.castSucc) (fun i => values i.castSucc))

/-- Distinct active variables evaluate to their own full ground value, even
when different variables happen to carry equal values. -/
theorem entriesSubst_value (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    (hi : Function.Injective vars) (i : Fin h) :
    entriesSubst h vars values (vars i) = groundTerm (values i) := by
  classical
  induction h with
  | zero => exact i.elim0
  | succ h ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [entriesSubst,replaceVar,groundTerm_subst]
    · have hn : vars j.castSucc ≠ vars (Fin.last h) := by
        intro he
        have hh := hi he
        have hv := congrArg Fin.val hh
        have hj := j.isLt
        simp only [Fin.val_castSucc,Fin.val_last] at hv
        omega
      simp only [entriesSubst,replaceVar,if_neg hn,Term.subst]
      exact ih _ _ (hi.comp (Fin.castSucc_injective _)) j

/-- A single source Subst can reach a continuation beside an unrelated frame,
using only source parallel rearrangements. -/
theorem subst_beside_context (x : V) (m : Term V) (a : Extended V) (p : Agent V) :
    Structural (.par (.par (.active x m) a) (.plain p))
      (.par (.par (.active x m) a) (.plain (p.subst (replaceVar x m)))) := by
  have rearrange (q : Agent V) :
      Structural (.par (.par (.active x m) a) (.plain q)) (.par a (.par (.active x m) (.plain q))) :=
    (Structural.parLeft _ (Structural.comm _ _)).trans (Structural.assoc _ _ _)
  exact (rearrange p).trans ((Structural.parRight a (Structural.substPlain x m p)).trans (rearrange _).symm)

/-- Each active substitution is distributed into the same plain process in
turn. The frame itself is retained exactly throughout the derivation. -/
theorem frameEntries_apply (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (p : Agent V) :
    Structural (.par (frameEntries h vars values) (.plain p))
      (.par (frameEntries h vars values) (.plain (p.subst (entriesSubst h vars values)))) := by
  induction h generalizing p with
  | zero => simpa only [entriesSubst,Agent.subst_var] using Structural.refl (.par (frameEntries 0 vars values) (.plain p))
  | succ h ih =>
    have hs := subst_beside_context (vars (Fin.last h)) (groundTerm (values (Fin.last h)))
      (frameEntries h (fun i => vars i.castSucc) (fun i => values i.castSucc)) p
    have hh := (Structural.assoc (.active (vars (Fin.last h)) (groundTerm (values (Fin.last h)))) _ _).trans
      ((Structural.parRight _ (ih (fun i => vars i.castSucc) (fun i => values i.castSucc)
        (p.subst (replaceVar (vars (Fin.last h)) (groundTerm (values (Fin.last h))))))).trans
          (Structural.assoc _ _ _).symm)
    have ht := hs.trans hh
    simpa only [frameEntries,entriesSubst,Agent.subst_subst] using ht

/-- Source active substitutions evaluate an arbitrary handle-using continuation
in the actual frame. This includes substitutions beneath further input binders. -/
theorem activeFrame_apply (φ : Frame restricted handles) (p : Agent (Fin handles)) :
    Structural (.par (activeFrame φ) (.plain p))
      (.par (activeFrame φ) (.plain (p.subst (fun i => groundTerm (φ.value i))))) := by
  have he : entriesSubst handles id φ.value = fun i => groundTerm (φ.value i) := by
    funext i
    exact entriesSubst_value handles id φ.value Function.injective_id i
  simpa only [activeFrame,he] using frameEntries_apply handles id φ.value p

/-- Evaluating a recipe and then embedding it equals substituting the frame's
full ground terms directly into that recipe. -/
theorem recipe_ground_eval (φ : Frame restricted handles) (r : Recipe handles) :
    r.subst (fun i => groundTerm (φ.value i)) = (groundTerm (φ.eval r) : Term (Fin handles)) := by
  simp only [groundTerm,Frame.eval,Term.subst_subst]

/-- The explicit frame exports exactly its listed variables, with no extra
variable introduced by the recursive presentation. -/
theorem frameEntries_exports_iff (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) (v : V) :
    (frameEntries h vars values).Exports v ↔ ∃ i, v=vars i := by
  induction h with
  | zero =>
    constructor
    · exact False.elim
    · rintro ⟨i,_⟩
      exact i.elim0
  | succ h ih =>
    change (v=vars (Fin.last h) ∨ (frameEntries h (fun i => vars i.castSucc) (fun i => values i.castSucc)).Exports v) ↔ _
    constructor
    · rintro (he | he)
      · exact ⟨Fin.last h,he⟩
      · obtain ⟨i,hi⟩ := (ih _ _).mp he
        exact ⟨i.castSucc,hi⟩
    · rintro ⟨i,he⟩
      revert he
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact Or.inl
      · intro hj
        exact Or.inr ((ih _ _).mpr ⟨j,hj⟩)

/-- Every variable available to an input recipe is actually exported by the
source frame, not merely a type-level handle without a defining substitution. -/
theorem activeFrame_exports (φ : Frame restricted handles) (i : Fin handles) :
    (activeFrame φ).Exports i :=
  (frameEntries_exports_iff handles id φ.value i).mpr ⟨i,rfl⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
