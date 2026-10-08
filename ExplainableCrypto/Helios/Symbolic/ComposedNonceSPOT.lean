import ExplainableCrypto.Helios.Symbolic.ComposedNonce
import ExplainableCrypto.Helios.Symbolic.NonceProtectionSPOT

namespace ExplainableCrypto.Helios.Symbolic.ComposedNonceSPOT
open NonceProtectionSPOT

/-- All public recipes and arbitrary remainders are quantified, without a
normal-form assumption on the target remainder. -/
theorem published_composed_nonce_excluded (n : Nat) (r : Recipe 4) (hr : r.Public {n})
    (rest : Ground) : ¬ EqE ((published n).eval r) (.binary .compose (.name n) rest) :=
  (published n).nonce_with_remainder_not_deducible (published_protected n) r hr (by simp) rest

theorem permuted_repeated_nonce_excluded (n : Nat) (r : Recipe 4) (hr : r.Public {n})
    (a b : Ground) : ¬ EqE ((published n).eval r)
      (.binary .compose (.binary .compose a (.name n)) (.binary .compose (.name n) b)) := by
  apply (published n).composed_nonce_not_deducible (n := n) (published_protected n) r hr (by simp)
  simp [Term.composeFactors]

def expanded (n : Nat) : Ground := .binary .compose (.name (n + 1)) (.name (n + 2))
def expanding (n : Nat) : Ground := .unary .fst (.binary .pair (expanded n) (.const .bottom))
def source (n : Nat) : Ground := .binary .compose (.binary .compose (.name n) (.name n)) (expanding n)
def target (n : Nat) : Ground := .binary .compose (.binary .compose (.name n) (.name n)) (expanded n)

theorem expanding_remainder_step (n : Nat) : ModuloStep (source n) (target n) :=
  (RootStep.fst (expanded n) (.const .bottom)).to_modulo.context
    (.binaryRight .compose (.binary .compose (.name n) (.name n)) .hole)

theorem expanding_remainder_keeps_nonce (n : Nat) :
    (Term.name (V := Empty) n).baseClass ∈ (target n).composeFactors ∧
    (source n).composeFactors.card = 3 ∧ (target n).composeFactors.card = 4 := by
  refine ⟨(expanding_remainder_step n).compose_name_mem ?_, ?_, ?_⟩
  · simp [source, Term.composeFactors]
  · simp [source, expanding, Term.composeFactors]
  · simp [target, expanded, Term.composeFactors]

theorem reducible_target_excluded (n : Nat) (r : Recipe 4) (hr : r.Public {n}) :
    ¬ EqE ((published n).eval r) (source n) ∧ ¬ Irreducible (source n) := by
  refine ⟨?_, fun h => h (target n) (expanding_remainder_step n)⟩
  apply (published n).composed_nonce_not_deducible (n := n) (published_protected n) r hr (by simp)
  simp [source, Term.composeFactors]

/-- The restricted nonce inside ciphertext randomness is not an exposed outer factor. -/
theorem protected_ciphertext_remains_available (n : Nat) :
    EqE ((published n).eval selectCipher) (NonceProtectionSPOT.cipher n) ∧
    (Term.name (V := Empty) n).baseClass ∉ (NonceProtectionSPOT.cipher n).composeFactors := by
  exact ⟨(public_ballot_projection n).2,
    (NonceProtectionSPOT.cipher n).nonce_safe_no_name_factor (restricted := {n}) (by simp [NonceProtectionSPOT.cipher, NonceProtectionSPOT.key, Term.nonceSafe]) (by simp)⟩

/-- An arbitrary syntactic occurrence can disappear outside the composition-factor scope. -/
theorem discarded_name_does_not_persist (n : Nat) :
    let t : Ground := .unary .fst (.binary .pair (.const .one) (.name n))
    ModuloStep t (.const .one) ∧ ¬ t.Public {n} ∧ (Term.const .one : Ground).Public {n} := by
  exact ⟨(RootStep.fst (.const .one) (.name n)).to_modulo,
    by simp [Term.Public], trivial⟩

end ExplainableCrypto.Helios.Symbolic.ComposedNonceSPOT
