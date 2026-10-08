import ExplainableCrypto.Helios.Symbolic.SourceScopedProgramCapture
import ExplainableCrypto.Helios.Symbolic.SourceCanonicalPolicyPadding

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- The actual old and program restrictions bind exactly the union policy.
This includes duplicates and requires no injectivity of the program name list. -/
theorem scoped_program_prefix_policy (hidden restricted : Finset Nat) (ns : List Nat) :
    (restrictionNames hidden restricted ++ ns.map SourceName.base).toFinset =
      (restrictionNames hidden (restricted ∪ ns.toFinset)).toFinset := by
  ext u
  cases u <;> simp [restrictionNames]

/-- Safely hoist program binders past the complete old frame, retain every
actual output local, then reconstruct the computed capture under that prefix. -/
theorem frame_scoped_program_capture_normalize (φ : Frame restricted handles)
    (p : ScopedTermProgram (Fin handles)) (hp : p.Hoistable)
    (hf : ∀ n ∈ p.names, n ∉ φ.nameSupport) :
    Structural
      ((Named.par (.embed ((Extended.activeFrame φ).rename some)) p.capture).rename Extended.outputHandle)
      (restrictNames (p.names.map SourceName.base)
        (.embed (Extended.frameProcess (φ.extend (φ.eval p.erase.value)) .nil))) := by
  let a := Named.embed ((Extended.activeFrame φ).rename some)
  have hf' : ∀ u ∈ p.names.map SourceName.base, u ∉ a.freeNames := by
    intro u hu
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hu
    simpa only [a,freeNames,Extended.nameSupport_rename,Extended.activeFrame_base_fresh_iff] using hf n hn
  have hh := (Structural.parRight a (p.capture_hoist hp)).trans
    ((Structural.par_restrictNames_right a _ _ hf').trans
      ((Structural.embedPar ((Extended.activeFrame φ).rename some) p.erase.capture).symm.restrictNames _))
  have hr := hh.rename Extended.outputHandle Extended.outputHandle.injective
  rw [restrictNames_rename] at hr
  exact hr.trans ((Structural.embed (Extended.frame_program_capture_normalize φ p.erase)).restrictNames _)

/-- The complete reconstructed frame carries every original and program base
restriction, rather than forgetting the new nonces when updating its policy. -/
theorem restricted_scoped_program_capture_normalize (φ : Frame restricted handles)
    (p : ScopedTermProgram (Fin handles)) (hp : p.Hoistable)
    (hf : ∀ n ∈ p.names, n ∉ φ.nameSupport) :
    Structural
      ((restrictNames (restrictionNames hidden restricted)
        (.par (.embed ((Extended.activeFrame φ).rename some)) p.capture)).rename Extended.outputHandle)
      (restrictedState hidden
        ⟨(φ.extend (φ.eval p.erase.value)).withPolicy (restricted ∪ p.names.toFinset),.nil⟩) := by
  have hs := (frame_scoped_program_capture_normalize φ p hp hf).restrictNames
    (restrictionNames hidden restricted)
  have ht := Structural.restrictNames_of_toFinset_eq
    (restrictionNames hidden restricted ++ p.names.map SourceName.base)
    (restrictionNames hidden (restricted ∪ p.names.toFinset))
    (scoped_program_prefix_policy hidden restricted p.names)
    (.embed (Extended.frameProcess (φ.extend (φ.eval p.erase.value)) .nil))
  rw [restrictNames_append] at ht
  simpa only [restrictNames_rename,restrictedState,Extended.frameProcess,Extended.activeFrame,Frame.withPolicy] using hs.trans ht

theorem restricted_scoped_program_capture_represents (φ : Frame restricted handles)
    (p : ScopedTermProgram (Fin handles)) (hp : p.Hoistable)
    (hf : ∀ n ∈ p.names, n ∉ φ.nameSupport) :
    (((restrictNames (restrictionNames hidden restricted)
      (.par (.embed ((Extended.activeFrame φ).rename some)) p.capture)).rename Extended.outputHandle)).RepresentsFrame
      hidden ((φ.extend (φ.eval p.erase.value)).withPolicy (restricted ∪ p.names.toFinset)) :=
  (restrictedState_represents _).structural (restricted_scoped_program_capture_normalize φ p hp hf).symm

/-- Actual interleaved scopes are retained by the output derivation, and its
full target normalizes to the complete frame with the combined private policy. -/
theorem restricted_scoped_program_output (φ : Frame restricted handles)
    (p : ScopedTermProgram (Fin handles)) (hp : p.Hoistable)
    (hf : ∀ n ∈ p.names, n ∉ φ.nameSupport) (c : Nat) (hc : c ∉ hidden) :
    ∃ b : Named (Option (Fin handles)),
      BoundOutput (restrictNames (restrictionNames hidden restricted)
        (.par (.embed (Extended.activeFrame φ)) (p.compile c))) c b ∧
      Structural (b.rename Extended.outputHandle)
        (restrictedState hidden
          ⟨(φ.extend (φ.eval p.erase.value)).withPolicy (restricted ∪ p.names.toFinset),.nil⟩) := by
  refine ⟨_,(BoundOutput.parRight (.embed (Extended.activeFrame φ)) (p.compile_output_capture c)).restrictNames _
    ((output_restriction_fresh_iff c).mpr hc),?_⟩
  exact restricted_scoped_program_capture_normalize φ p hp hf

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
