import ExplainableCrypto.Helios.Symbolic.SourcePresentationRigidity
import ExplainableCrypto.Helios.Symbolic.SourceElectionOpeningInvariant

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V W : Type}

/-- All actual name allocations retain uniqueness of remaining local variable
solutions. The name choices stay outside the local rigidity predicate. -/
def LocallyRigid (a : Named V) : Prop :=
  ∀ (ρ : NameAssignment) (ns : List SourceName) (b : Extended V),
    Opens a ρ ns b → ∀ env, b.Rigid env

theorem LocallyRigid.embed (a : Extended V)
    (h : ∀ (ρ : NameAssignment) env, (a.mapNames ρ.base ρ.channel).Rigid env) :
    (Named.embed a).LocallyRigid := by
  intro ρ ns b hb env
  cases hb
  exact h ρ env

theorem LocallyRigid.newName {a : Named V} (h : a.LocallyRigid) (n : SourceName) :
    (Named.newName n a).LocallyRigid := by
  intro ρ ns b hb env
  cases hb with
  | newName _ v hb _ => exact h _ _ _ hb env

theorem LocallyRigid.restrictNames {a : Named V} (h : a.LocallyRigid) (ns : List SourceName) :
    (restrictNames ns a).LocallyRigid := by
  induction ns with
  | nil => exact h
  | cons n ns ih => exact ih.newName n

/-- A bijective public-handle change transports all environments, including
the Option-to-Fin naming used after publication. -/
theorem LocallyRigid.rename {a : Named V} (h : a.LocallyRigid) (e : V ≃ W) :
    (a.rename e).LocallyRigid := by
  intro ρ ns b hb env
  have ho : Opens a ρ ns (b.rename e.symm) := by
    simpa only [Named.rename_comp,Equiv.symm_comp_self,Named.rename_id] using hb.rename e.symm
  have hr := h ρ ns _ ho (fun v => env (e v))
  have he : (fun v => env (e (e.symm v))) = env := by
    funext v; rw [e.apply_symm_apply]
  simpa only [Extended.rigid_rename,he] using hr

/-- Removing plain code never changes the available name allocations. -/
theorem Opens.of_frameOf {a : Named V} {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended V} (h : Opens a.frameOf ρ ns b) :
    ∃ c, Opens a ρ ns c ∧ c.frameOf = b := by
  induction a generalizing ρ ns with
  | embed a =>
    cases h
    exact ⟨_,.embed a ρ,Extended.frameOf_mapNames a ρ.base ρ.channel⟩
  | par a d ih ij =>
    cases h with
    | par ha hd hf =>
      obtain ⟨c,hc,rfl⟩ := ih ha
      obtain ⟨e,he,rfl⟩ := ij hd
      exact ⟨.par c e,.par hc he hf,rfl⟩
  | newName n a ih =>
    cases h with
    | newName _ v ha hf =>
      obtain ⟨c,hc,rfl⟩ := ih ha
      exact ⟨c,.newName n v hc hf,rfl⟩
  | newVar a ih =>
    cases h with
    | newVar ha =>
      obtain ⟨c,hc,rfl⟩ := ih ha
      exact ⟨.newVar c,.newVar hc,rfl⟩

theorem locallyRigid_frameOf (a : Named V) : a.frameOf.LocallyRigid ↔ a.LocallyRigid := by
  constructor
  · intro h ρ ns b hb env
    exact (Extended.rigid_frameOf b env).mp (h ρ ns b.frameOf hb.frameOf env)
  · intro h ρ ns b hb env
    obtain ⟨c,hc,rfl⟩ := hb.of_frameOf
    exact (Extended.rigid_frameOf c env).mpr (h ρ ns c hc env)

/-- Arbitrary name-scoped structural detours preserve the invariant, using
actual binder-structural opening witnesses. -/
theorem Structural.locallyRigid {a b : Named V} (h : Structural a b) :
    a.LocallyRigid ↔ b.LocallyRigid := by
  have go {a b : Named V} (h : Structural a b) (ha : a.LocallyRigid) : b.LocallyRigid := by
    intro ρ ns c hc env
    obtain ⟨ms,d,hd,_,he⟩ := h.symm.transport_binder_opening ρ ns c ∅ hc (by simp)
    exact (he.rigid env).mpr (ha ρ ms d hd env)
  exact ⟨go h,go h.symm⟩

theorem Reduction.locallyRigid {a b : Named V} (h : Reduction a b) :
    a.LocallyRigid ↔ b.LocallyRigid :=
  (locallyRigid_frameOf a).symm.trans (h.frameOf.locallyRigid.trans (locallyRigid_frameOf b))

theorem FreeStep.locallyRigid {a b : Named V} {l : Extended.FreeLabel V} (h : FreeStep a l b) :
    a.LocallyRigid ↔ b.LocallyRigid :=
  (locallyRigid_frameOf a).symm.trans (h.frameOf.locallyRigid.trans (locallyRigid_frameOf b))

/-- Every target environment decomposes into the exported value and the old
environment. Unsatisfiable local choices remain vacuously rigid. -/
theorem LocallyRigid.newVar_body {a : Named (Option V)} (h : (Named.newVar a).LocallyRigid) :
    a.LocallyRigid := by
  intro ρ ns b hb env
  have hr := h ρ ns (.newVar b) (.newVar hb) (fun v => env (some v))
  have he : extendEnv (fun v => env (some v)) (env none) = env := by
    funext v; cases v <;> rfl
  simpa only [he] using Extended.rigid_newVar_body hr (env none)

/-- Reclosing the new output handle retains exactly the old local obligations. -/
theorem BoundOutput.locallyRigid_reclose {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) : (Named.newVar b).LocallyRigid ↔ a.LocallyRigid :=
  (locallyRigid_frameOf (.newVar b)).symm.trans
    (h.frameOf_reclose.locallyRigid.trans (locallyRigid_frameOf a))

/-- All remaining local choices stay rigid through every original Named output
rule, including name/variable Scope and structural/alpha closure. -/
theorem BoundOutput.locallyRigid {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (ha : a.LocallyRigid) : b.LocallyRigid :=
  ((h.locallyRigid_reclose).mpr ha).newVar_body

theorem RepresentsFrame.locallyRigid {restricted hidden : Finset Nat} {handles : Nat}
    {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) : a.LocallyRigid :=
  fun _ _ _ ho env => h.opening_rigid ho env

theorem restrictedState_locallyRigid {restricted hidden : Finset Nat} {handles : Nat}
    (s : ScopedState restricted handles) : (restrictedState hidden s).LocallyRigid :=
  (restrictedState_represents s).locallyRigid

/-- The cyclic joint partner fails this reachable invariant in a literal
opening, irrespective of the complete frame and live plain body beside it. -/
theorem frame_with_unconstrained_local_not_locallyRigid {restricted : Finset Nat} {handles : Nat}
    (φ : Frame restricted handles) (p : Agent Empty) :
    ¬ (Named.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))).LocallyRigid := by
  intro h
  have ho : Opens (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none)))))
      NameAssignment.literal [] (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none)))) := by
    simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using Opens.embed _ NameAssignment.literal
  have hr := h _ _ _ ho φ.value
  have hs : (Extended.frameProcess φ p).Satisfies φ.value := by
    change (Extended.activeFrame φ).Satisfies φ.value ∧ True
    exact ⟨(Extended.activeFrame_satisfies_iff φ φ.value).mpr (fun _ => .refl _),True.intro⟩
  exact Extended.unconstrained_local_not_rigid φ.value (hr hs ⟨.name 40,.refl _⟩).2

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
