import ExplainableCrypto.Helios.Symbolic.SourceFrameActions
import ExplainableCrypto.Helios.Symbolic.SourceInterpretationFrames
import ExplainableCrypto.Helios.Symbolic.SourceNameRestrictionBridge

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

theorem Extended.frameEntries_frameOf (h : Nat) (vars : Fin h → V) (values : Fin h → Ground) :
    (Extended.frameEntries h vars values).frameOf = Extended.frameEntries h vars values := by
  induction h with
  | zero => rfl
  | succ h ih => simp only [Extended.frameEntries,Extended.frameOf,ih]

theorem Extended.activeFrame_frameOf (φ : Frame restricted handles) :
    (Extended.activeFrame φ).frameOf = Extended.activeFrame φ :=
  Extended.frameEntries_frameOf _ _ _

theorem Extended.frameProcess_frameOf (φ : Frame restricted handles) (p : Agent Empty) :
    Extended.Structural (Extended.frameProcess φ p).frameOf (Extended.activeFrame φ) := by
  simpa only [Extended.frameProcess,Extended.frameOf,Extended.activeFrame_frameOf] using
    Extended.Structural.zero (Extended.activeFrame φ)

theorem Named.restrictedState_frameOf (hidden : Finset Nat) (p : ScopedState restricted handles) :
    Named.Structural (Named.restrictedState hidden p).frameOf
      (Named.restrictNames (restrictionNames hidden restricted) (.embed (Extended.activeFrame p.frame))) := by
  simpa only [Named.restrictedState,Named.frameOf_restrictNames,Named.frameOf] using
    (Named.Structural.embed (Extended.frameProcess_frameOf p.frame p.body)).restrictNames
      (restrictionNames hidden restricted)

/-- Frame extraction retains exactly the active constraints of any supplied
realization; the resulting frame realizes Nil. -/
theorem Extended.Realizes.frameOf {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (h : a.Realizes env p) : a.frameOf.Realizes env .nil := by
  induction a generalizing p with
  | plain => exact .refl _
  | active => exact ⟨h.1,.refl _⟩
  | par a b ha hb =>
    obtain ⟨r,s,hr,hs,_⟩ := h
    exact ⟨.nil,.nil,ha hr,hb hs,.of_parEq (.zero _)⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    exact ⟨m,ih hm⟩

/-- Satisfying a projected frame supplies some interpreted process for the
original syntax; this statement does not choose a canonical process body. -/
theorem Extended.realizes_of_frameOf {a : Extended V} {env : V → Ground} {p : Agent Empty}
    (h : a.frameOf.Realizes env p) : ∃ q, a.Realizes env q := by
  induction a generalizing p with
  | plain a => exact ⟨a.subst env,.refl _⟩
  | active => exact ⟨p,h⟩
  | par a b ha hb =>
    obtain ⟨r,s,hr,hs,_⟩ := h
    obtain ⟨r',hr'⟩ := ha hr
    obtain ⟨s',hs'⟩ := hb hs
    exact ⟨.par r' s',r',s',hr',hs',.refl _⟩
  | newVar a ih =>
    obtain ⟨m,hm⟩ := h
    obtain ⟨q,hq⟩ := ih hm
    exact ⟨q,m,hq⟩

theorem Extended.frameOf_realizes_iff (a : Extended V) (env : V → Ground) :
    a.frameOf.Realizes env .nil ↔ ∃ p, a.Realizes env p :=
  ⟨Extended.realizes_of_frameOf,fun ⟨_,h⟩ => h.frameOf⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
