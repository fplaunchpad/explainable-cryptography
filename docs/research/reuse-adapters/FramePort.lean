import ExplainableCrypto.Helios.Symbolic.SourceFrameStructure

/-! An isolated Lean port of AFP Psi_Calculi.Frame.frameResChainFresh and
one-binder frameChainAlpha. This imports the actual completed source syntax,
not the original freeNames_restrictNames proof targeted for replacement. The
source alpha rule requires freshness against all names; AFP's nominal statement
has its own support/permutation premises. No imported Isabelle proof is claimed. -/
namespace HeliosReuseAudit.FramePort
open ExplainableCrypto.Helios.Symbolic Historical General Source
variable {V : Type}

theorem frameResChainFresh (xs : List SourceName) (a : Named V) (x : SourceName) :
    x ∉ (Named.restrictNames xs a).freeNames ↔ x ∈ xs ∨ x ∉ a.freeNames := by
  induction xs with
  | nil => simp [Named.restrictNames]
  | cons y xs ih =>
    change x ∉ ((Named.restrictNames xs a).freeNames.erase y) ↔ _
    simp only [Finset.mem_erase,not_and_or,not_not,ih,List.mem_cons,or_assoc]

/-- Exact interface of the completed source lemma, derived without importing
its implementation. This is the concrete replacement candidate. -/
theorem freeNames_restrictNames_replacement (xs : List SourceName) (a : Named V) :
    (Named.restrictNames xs a).freeNames = a.freeNames \ xs.toFinset := by
  ext x
  have h := frameResChainFresh xs a x
  simp only [Finset.mem_sdiff,List.mem_toFinset] at *
  tauto

/-- Original structural equality on complete frames, with the actual source
freshness policy, rather than nominal equality assumed for a new representation. -/
theorem frameChainAlphaOne (a : Named V) (n m : Nat) (hf : SourceName.base m ∉ a.allNames) :
    Named.Structural (Named.newName (.base n) a).frameOf
      (Named.newName (.base m) (a.mapNames (Equiv.swap n m) id)).frameOf :=
  (Named.Structural.alphaBase a n m hf).frameOf

abbrev fullFrame : Named (Fin 1) := .embed (.active 0
  (.spk (.name 40) (.name 41) (.const .one) (.binary .pair (.name 40) (.name 41))))

theorem alpha_retains_every_proof_field :
    Named.Structural (Named.newName (.base 40) fullFrame).frameOf
      (Named.newName (.base 42) (.embed (.active (0 : Fin 1)
        (.spk (.name 42) (.name 41) (.const .one) (.binary .pair (.name 42) (.name 41)))))).frameOf := by
  simpa only [fullFrame,Named.mapNames,Extended.mapNames,Term.mapNames,Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (by decide : (41 : Nat) ≠ 40) (by decide : (41 : Nat) ≠ 42)] using
    frameChainAlphaOne fullFrame 40 42 (by decide)

theorem public_literal_cannot_be_freshened_into : SourceName.base 41 ∈ fullFrame.allNames := by decide

theorem full_scope_distinguishes_bound_and_public :
    SourceName.base 40 ∉ (Named.restrictNames [.base 40] fullFrame).freeNames ∧
    SourceName.base 41 ∈ (Named.restrictNames [.base 40] fullFrame).freeNames := by decide

#print axioms frameResChainFresh
#print axioms freeNames_restrictNames_replacement
#print axioms frameChainAlphaOne
#print axioms alpha_retains_every_proof_field
#print axioms public_literal_cannot_be_freshened_into
#print axioms full_scope_distinguishes_bound_and_public
end HeliosReuseAudit.FramePort
