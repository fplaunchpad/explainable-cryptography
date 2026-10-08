import ExplainableCrypto.Helios.Symbolic.SourceNamedRigidityBoundary

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {V : Type} {restricted hidden : Finset Nat} {handles : Nat}

/-- A chosen name opening retains exactly its allocation when plain code is
removed to obtain the complete source frame. -/
theorem Opens.frameOf {a : Named V} {ρ : NameAssignment} {ns : List SourceName} {b : Extended V}
    (h : Opens a ρ ns b) : Opens a.frameOf ρ ns b.frameOf := by
  induction h with
  | embed a ρ =>
    simpa only [Named.frameOf,Extended.frameOf_mapNames] using Opens.embed a.frameOf ρ
  | par _ _ hd ih ij => exact .par ih ij hd
  | newName n v _ hf ih => exact .newName n v ih hf
  | newVar _ ih => exact .newVar ih

/-- A canonical active frame has no local variable choices, under any actual
name allocation. No injectivity or freshness premise is needed for rigidity. -/
theorem Opens.canonicalFrame_rigid {φ : Frame restricted handles} {ρ : NameAssignment}
    {ns : List SourceName} {b : Extended (Fin handles)}
    (h : Opens (canonicalFrame hidden φ) ρ ns b) (env : Fin handles → Ground) : b.Rigid env := by
  have go (names : List SourceName) (ρ : NameAssignment) (ns : List SourceName) (b : Extended (Fin handles))
      (ho : Opens (restrictNames names (.embed (Extended.activeFrame φ))) ρ ns b) : b.Rigid env := by
    induction names generalizing ρ ns b with
    | nil =>
      cases ho
      rw [Extended.activeFrame_mapNames]
      exact Extended.activeFrame_rigid _ env
    | cons n names ih => cases ho with
      | newName _ v ho hf => exact ih _ _ _ ho
  exact go _ _ _ _ h

/-- A genuine source frame presentation forces rigidity in every chosen
opening and every environment, not merely the existence of a semantic class. -/
theorem RepresentsFrame.opening_rigid {a : Named (Fin handles)} {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) {ρ : NameAssignment} {ns : List SourceName}
    {b : Extended (Fin handles)} (ho : Opens a ρ ns b) (env : Fin handles → Ground) : b.Rigid env := by
  obtain ⟨ms,c,hc,_,he⟩ := h.transport_binder_opening ρ ns b.frameOf ∅ ho.frameOf (by simp)
  exact (Extended.rigid_frameOf b env).mp ((he.rigid env).mpr (hc.canonicalFrame_rigid env))

/-- The cyclic semantic partner admits no complete ground frame presentation,
with any policy, values or hidden names on the same public handle domain. -/
theorem frame_with_unconstrained_local_no_presentation (φ : Frame restricted handles) (p : Agent Empty)
    {restricted' : Finset Nat} (ψ : Frame restricted' handles) (hidden : Finset Nat) :
    ¬ (Named.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))).RepresentsFrame hidden ψ := by
  intro h
  have ho : Opens (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none)))))
      NameAssignment.literal [] (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none)))) := by
    simpa only [show NameAssignment.literal.base = id from rfl,
      show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using Opens.embed _ NameAssignment.literal
  have hr := h.opening_rigid ho φ.value
  have hs : (Extended.frameProcess φ p).Satisfies φ.value := by
    change (Extended.activeFrame φ).Satisfies φ.value ∧ True
    exact ⟨(Extended.activeFrame_satisfies_iff φ φ.value).mpr (fun _ => .refl _),True.intro⟩
  exact Extended.unconstrained_local_not_rigid φ.value (hr hs ⟨.name 40,.refl _⟩).2

/-- The presentable-frame static relation cannot admit the cyclic process
on either side, regardless of its semantic joint-opening partner. -/
theorem frame_with_unconstrained_local_no_staticEq (φ : Frame restricted handles) (p : Agent Empty)
    (d : Named (Fin handles)) :
    ¬ StaticEq (.embed (.par (Extended.frameProcess φ p) (.newVar (.active none (.var none))))) d := by
  rintro ⟨hidden,_,ψ,_,hp,_,_⟩
  exact frame_with_unconstrained_local_no_presentation φ p ψ hidden hp

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
