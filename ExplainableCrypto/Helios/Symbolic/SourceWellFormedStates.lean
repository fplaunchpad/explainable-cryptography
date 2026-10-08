import ExplainableCrypto.Helios.Symbolic.SourceUniqueDefinitions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- All free variable uses and active domains belong to the allowed scope.
A restriction binds only None; definitions in other parallel components remain
available through the common outer scope. -/
def VarsIn : {V : Type} → (V → Prop) → Extended V → Prop
  | _, s, .plain p => p.VarsIn s
  | _, s, .active x m => s x ∧ m.VarsIn s
  | _, s, .par a b => a.VarsIn s ∧ b.VarsIn s
  | _, s, .newVar a => a.VarsIn (binderScope s)

/-- Source closedness for variables: every free use is defined by an exported
active substitution. Restricted and input-bound variables are handled locally. -/
def Closed (a : Extended V) : Prop := a.VarsIn a.Exports

/-- The source's active-definition and closed-variable requirements for this
fragment. Name restriction and full source admissibility remain separate. -/
def WellFormed (a : Extended V) : Prop := a.UniqueDefinitions ∧ a.Closed

theorem varsIn_all (a : Extended V) : a.VarsIn (fun _ => True) := by
  induction a with
  | plain p => exact p.varsIn_all
  | active x m => exact ⟨True.intro,m.varsIn_all⟩
  | par a b ha hb => exact ⟨ha,hb⟩
  | newVar a ha =>
    rename_i V'
    have he : binderScope (fun _ : V' => True) = (fun _ => True) := by funext v; cases v <;> rfl
    simpa only [VarsIn,he] using ha

theorem varsIn_mono (a : Extended V) {s t : V → Prop} (h : a.VarsIn s) (hs : ∀ v, s v → t v) :
    a.VarsIn t := by
  induction a with
  | plain p => exact p.varsIn_mono h hs
  | active x m => exact ⟨hs x h.1,m.varsIn_mono h.2 hs⟩
  | par a b ha hb => exact ⟨ha h.1 hs,hb h.2 hs⟩
  | newVar a ha =>
    apply ha h
    intro v hv
    cases v with
    | none => trivial
    | some v => exact hs v hv

theorem closed_of_all_exports (a : Extended V) (h : ∀ v, a.Exports v) : a.Closed :=
  a.varsIn_mono a.varsIn_all (fun v _ => h v)

theorem closed_empty (a : Extended Empty) : a.Closed :=
  closed_of_all_exports a (fun v => v.elim)

/-- Frame entries have unique definitions whenever their variable names are
injective. Ground values can repeat without violating this condition. -/
theorem frameEntries_unique (h : Nat) (vars : Fin h → V) (values : Fin h → Ground)
    (hi : Function.Injective vars) : (frameEntries h vars values).UniqueDefinitions := by
  induction h with
  | zero => trivial
  | succ h ih =>
    refine ⟨True.intro,ih _ _ (hi.comp (Fin.castSucc_injective _)),?_⟩
    intro v ⟨hv,he⟩
    obtain ⟨j,hj⟩ := (frameEntries_exports_iff h _ _ v).mp he
    have hh := hi (hv.symm.trans hj)
    have hh' := congrArg Fin.val hh
    have hj' := j.isLt
    simp only [Fin.val_last,Fin.val_castSucc] at hh'
    omega

/-- Every actual public active frame is closed and has one definition per
handle, independently of the cryptographic values stored at those handles. -/
theorem activeFrame_wellFormed (φ : Frame restricted handles) : (activeFrame φ).WellFormed :=
  ⟨frameEntries_unique handles id φ.value Function.injective_id,
    closed_of_all_exports _ (activeFrame_exports φ)⟩

/-- The canonical source frame/process representation is a well-formed closed
extended state at every stage, with no reachability assumption needed. -/
theorem frameProcess_wellFormed (φ : Frame restricted handles) (p : Agent Empty) :
    (frameProcess φ p).WellFormed := by
  refine ⟨⟨(activeFrame_wellFormed φ).1,True.intro,?_⟩,?_⟩
  · intro v h
    exact h.2
  · exact closed_of_all_exports _ (fun v => Or.inl (activeFrame_exports φ v))

/-- A fresh active let introduces exactly its one required restricted
substitution; a plain input binder is not mistaken for another active binding. -/
theorem letTerm_unique (m : Term V) (p : Agent (Option V)) : (letTerm m p).UniqueDefinitions := by
  refine ⟨⟨True.intro,True.intro,?_⟩,Or.inl rfl⟩
  intro v h
  exact h.2

theorem ground_let_wellFormed (m : Ground) (p : Agent (Option Empty)) : (letTerm m p).WellFormed :=
  ⟨letTerm_unique m p,closed_empty _⟩

/-- The raw bound-output target has one new definition, keeps all old ones and
is closed before converting its fresh binder to the canonical last handle. -/
theorem frame_capture_wellFormed (φ : Frame restricted handles) (m : Ground) (p : Agent Empty) :
    (Extended.par ((activeFrame φ).rename some) (capture (groundTerm m) (groundAgent p))).WellFormed := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · exact (uniqueDefinitions_rename_iff _ some (Option.some_injective _)).mpr (activeFrame_wellFormed φ).1
  · exact ⟨True.intro,True.intro,fun _ h => h.2⟩
  · intro v ⟨hv,hc⟩
    have he := (capture_exports_iff _ _ v).mp hc
    subst v
    exact rename_some_no_fresh _ hv
  · apply closed_of_all_exports
    intro v
    cases v with
    | none => exact Or.inr ((capture_exports_iff _ _ _).mpr rfl)
    | some v => exact Or.inl ((rename_exports _ some (Option.some_injective _) v).mpr (activeFrame_exports φ v))
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
