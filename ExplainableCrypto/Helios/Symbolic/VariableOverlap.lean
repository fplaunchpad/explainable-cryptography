import ExplainableCrypto.Helios.Symbolic.Confluence
import ExplainableCrypto.Helios.Symbolic.ReductionSubstitution
import ExplainableCrypto.Helios.Symbolic.RootReduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

/-- A root step competes with a step inside one occurrence of a schema variable.
Synchronising the remaining copies joins the peak without local confluence.
The explicit schema context does not assert coverage of fixed-position or E0 overlaps. -/
theorem variable_peak_joined (c : Context V) (v : V) (r : Term V)
    (hr : RootStep (c.fill (.var v)) r) (σ : V → Term W) {b : Term W}
    (hs : ModuloStep (σ v) b) :
    ModuloStep ((c.fill (.var v)).subst σ) (r.subst σ) ∧
    ModuloStep ((c.fill (.var v)).subst σ) ((c.subst σ).fill b) ∧
    JoinModulo (r.subst σ) ((c.subst σ).fill b) := by
  classical
  let τ : V → Term W := fun w => if w = v then b else σ w
  have hτ : ∀ w, ReducesModulo (σ w) (τ w) := by
    intro w
    by_cases hw : w = v
    · subst w
      simpa [τ] using ReducesModulo.single hs
    · simpa [τ, hw] using ReducesModulo.refl (σ w)
  refine ⟨(hr.subst σ).to_modulo, ?_, ?_⟩
  · simpa only [Context.subst_fill, Term.subst] using hs.context (c.subst σ)
  · refine ⟨r.subst τ, .subst_congr hτ r, ?_⟩
    have hroot : ModuloStep ((c.subst τ).fill b) (r.subst τ) := by
      simpa [Context.subst_fill, Term.subst, τ] using
        (hr.subst τ).to_modulo
    exact (c.subst_fill_reduces hτ b).trans (.single hroot)

namespace VariableOverlapSPOT

abbrev oldKey : Term Nat := .unary .fst (.binary .pair (.name 0) (.const .bottom))
abbrev enc (k : Term Nat) : Term Nat := .ternary .penc (.unary .pk k) (.name 1) (.const .one)
abbrev start : Term Nat := .binary .dec oldKey (enc oldKey)
abbrev inner : Term Nat := .binary .dec (.name 0) (enc oldKey)

/-- Both branches start at the same literal decryption; the result is one. -/
theorem decrypt_variable_peak : ModuloStep start (.const .one) ∧
    ModuloStep start inner ∧ JoinModulo (.const .one) inner := by
  let c : Context Nat := .binaryLeft .dec .hole (enc (.var 0))
  exact variable_peak_joined c 0 (.const .one)
    (RootStep.decrypt (.var 0) (.name 1) (.const .one)) (fun _ => oldKey)
    (RootStep.fst (.name 0) (.const .bottom)).to_modulo

/-- The interrupted match is a real loss of raw root applicability. -/
theorem one_copy_changed_no_root_match : (rootReduce inner).map Subtype.val = none := by
  decide

/-- Copy synchronisation restores actual progress to the expected plaintext. -/
theorem remaining_copy_reduces : ReducesModulo inner (.const .one) := by
  have h := (RootStep.fst (V := Nat) (.name 0) (.const .bottom)).to_modulo.context
    (.binaryRight .dec (.name 0)
      (.ternaryFirst .penc (.unary .pk .hole) (.name 1) (.const .one)))
  exact .head h (.single (RootStep.decrypt (.name 0) (.name 1) (.const .one)).to_modulo)

/-- E6 repeats the ciphertext and the key: synchronise all residual copies. -/
theorem partial_decrypt_variable_peak :
    let source : Term Nat := .binary .dec (.binary .partialDecrypt oldKey (enc oldKey)) (enc oldKey)
    let branch : Term Nat := .binary .dec (.binary .partialDecrypt (.name 0) (enc oldKey)) (enc oldKey)
    ModuloStep source (.const .one) ∧ ModuloStep source branch ∧ JoinModulo (.const .one) branch := by
  let c : Context Nat := .binaryLeft .dec
    (.binaryLeft .partialDecrypt .hole (enc (.var 0))) (enc (.var 0))
  exact variable_peak_joined c 0 (.const .one)
    (RootStep.partial_decrypt (.var 0) (.name 1) (.const .one)) (fun _ => oldKey)
    (RootStep.fst (.name 0) (.const .bottom)).to_modulo

abbrev ballot (k : Term Nat) (bit : Constant) : Term Nat :=
  .ternary .penc k (.name 1) (.const bit)

/-- E8 repeats the public key in the ciphertext and the proof. -/
theorem check_zero_variable_peak :
    let ball := ballot oldKey .zero
    let proof := Term.spk oldKey (.name 1) (.const .zero) ball
    ModuloStep (.ternary .checkspk oldKey ball proof) (.const .ok) ∧
    ModuloStep (.ternary .checkspk oldKey ball proof) (.ternary .checkspk (.name 0) ball proof) ∧
    JoinModulo (.const .ok) (.ternary .checkspk (.name 0) ball proof) := by
  let c : Context Nat := .ternaryFirst .checkspk .hole (ballot (.var 0) .zero)
    (.spk (.var 0) (.name 1) (.const .zero) (ballot (.var 0) .zero))
  exact variable_peak_joined c 0 (.const .ok) (RootStep.check_zero (.var 0) (.name 1))
    (fun _ => oldKey) (RootStep.fst (.name 0) (.const .bottom)).to_modulo

/-- The one branch must also verify, rather than always producing a zero proof. -/
theorem check_one_variable_peak :
    let ball := ballot oldKey .one
    let proof := Term.spk oldKey (.name 1) (.const .one) ball
    ModuloStep (.ternary .checkspk oldKey ball proof) (.const .ok) ∧
    ModuloStep (.ternary .checkspk oldKey ball proof) (.ternary .checkspk (.name 0) ball proof) ∧
    JoinModulo (.const .ok) (.ternary .checkspk (.name 0) ball proof) := by
  let c : Context Nat := .ternaryFirst .checkspk .hole (ballot (.var 0) .one)
    (.spk (.var 0) (.name 1) (.const .one) (ballot (.var 0) .one))
  exact variable_peak_joined c 0 (.const .ok) (RootStep.check_one (.var 0) (.name 1))
    (fun _ => oldKey) (RootStep.fst (.name 0) (.const .bottom)).to_modulo

end VariableOverlapSPOT
end ExplainableCrypto.Helios.Symbolic
