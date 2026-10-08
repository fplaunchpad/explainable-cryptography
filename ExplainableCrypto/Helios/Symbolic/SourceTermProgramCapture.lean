import ExplainableCrypto.Helios.Symbolic.SourceLocalCaptureNormalization
import ExplainableCrypto.Helios.Symbolic.SourceTermProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.TermProgram

/-- The actual target produced by output through every original local Scope.
Each enclosing provider remains local and is exchanged with the exported None.
This describes syntax; the original BoundOutput derivation is proved below. -/
def capture : {V : Type} → TermProgram V → Extended (Option V)
  | _, .result m => Extended.capture m .nil
  | _, .letTerm m p => .newVar
      ((Extended.par ((Extended.active none (shiftTerm m)).rename some) p.capture).rename Extended.swapBinders)

variable {V : Type}

/-- The actual raw target retains every local restriction introduced by the
program. Output is derived through Scope, without normalizing the source first. -/
theorem compile_output_capture (p : TermProgram V) (c : Nat) :
    Extended.BoundOutput (p.compile c) c p.capture := by
  induction p with
  | result m => exact Extended.message_output c m .nil
  | letTerm m p ih => exact .scope (.parRight _ ih)

/-- Dependent local definitions eliminate after the actual Scope exchanges,
leaving the complete computed term at the fresh public variable. -/
theorem capture_normalizes (p : TermProgram V) :
    Extended.Structural p.capture (Extended.capture p.value .nil) := by
  induction p with
  | result => exact .refl _
  | letTerm m p ih =>
    have hs := Extended.Structural.newVar
      ((Extended.Structural.parRight ((Extended.active none (shiftTerm m)).rename some) ih).rename Extended.swapBinders Extended.swapBinders_involutive.injective)
    exact hs.trans (Extended.scope_capture_normalize m p.value .nil)

theorem capture_exports_iff (p : TermProgram V) (v : Option V) :
    p.capture.Exports v ↔ v = none := by
  simpa only [Extended.capture,Extended.Exports,or_false] using p.capture_normalizes.exports v

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.TermProgram

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- All local providers remain in the raw output target before normalization;
the old public frame then reconstructs the full computed public value. -/
theorem frame_program_capture_normalize (φ : Frame restricted handles) (p : TermProgram (Fin handles)) :
    Structural ((Extended.par ((activeFrame φ).rename some) p.capture).rename outputHandle)
      (frameProcess (φ.extend (φ.eval p.value)) .nil) := by
  have hs := (Structural.parRight ((activeFrame φ).rename some) p.capture_normalizes).rename
    outputHandle outputHandle.injective
  exact hs.trans (frame_recipe_capture_normalize φ p.value .nil)

/-- The same raw target has both an actual Scope-derived output and a complete
canonical frame reconstruction, with no target-normalization premise. -/
theorem frame_program_output (φ : Frame restricted handles) (p : TermProgram (Fin handles)) (c : Nat) :
    BoundOutput (.par (activeFrame φ) (p.compile c)) c
      (.par ((activeFrame φ).rename some) p.capture) ∧
    Structural ((Extended.par ((activeFrame φ).rename some) p.capture).rename outputHandle)
      (frameProcess (φ.extend (φ.eval p.value)) .nil) :=
  ⟨.parRight _ (p.compile_output_capture c),frame_program_capture_normalize φ p⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

theorem restricted_program_capture_normalize (φ : Frame restricted handles) (p : TermProgram (Fin handles)) :
    Structural
      ((restrictNames (restrictionNames hidden restricted)
        (.embed (.par ((Extended.activeFrame φ).rename some) p.capture))).rename Extended.outputHandle)
      (restrictedState hidden ⟨φ.extend (φ.eval p.value),.nil⟩) := by
  simpa only [restrictNames_rename,rename,restrictedState] using
    (Structural.embed (Extended.frame_program_capture_normalize φ p)).restrictNames
      (restrictionNames hidden restricted)

theorem restricted_program_capture_represents (φ : Frame restricted handles) (p : TermProgram (Fin handles)) :
    (((restrictNames (restrictionNames hidden restricted)
      (.embed (.par ((Extended.activeFrame φ).rename some) p.capture))).rename Extended.outputHandle)).RepresentsFrame
      hidden (φ.extend (φ.eval p.value)) :=
  (restrictedState_represents _).structural (restricted_program_capture_normalize φ p).symm

/-- Sorted name restrictions remain around both the complete old providers and
the dependent local computation, as well as its entire raw output target. -/
theorem restricted_program_output (φ : Frame restricted handles) (p : TermProgram (Fin handles))
    (c : Nat) (hc : c ∉ hidden) :
    ∃ b : Named (Option (Fin handles)),
      BoundOutput (restrictNames (restrictionNames hidden restricted)
        (.embed (.par (Extended.activeFrame φ) (p.compile c)))) c b ∧
      Structural (b.rename Extended.outputHandle)
        (restrictedState hidden ⟨φ.extend (φ.eval p.value),.nil⟩) := by
  obtain ⟨ho,hs⟩ := Extended.frame_program_output φ p c
  refine ⟨_,(BoundOutput.embed ho).restrictNames _ ((output_restriction_fresh_iff c).mpr hc),?_⟩
  simpa only [restrictNames_rename,rename,restrictedState] using
    (Structural.embed hs).restrictNames (restrictionNames hidden restricted)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
