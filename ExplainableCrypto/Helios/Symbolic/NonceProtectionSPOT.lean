import ExplainableCrypto.Helios.Symbolic.NonceNonDeducibility

namespace ExplainableCrypto.Helios.Symbolic.NonceProtectionSPOT

def key (n : Nat) : Ground := .unary .pk (.name (n + 1))
def cipher (n : Nat) : Ground := .ternary .penc (key n) (.name n) (.const .one)
def proof (n : Nat) : Ground := .spk (key n) (.name n) (.const .one) (cipher n)
def ballotTail (n : Nat) : Ground := .binary .pair (proof n) (.binary .pair (proof n) (.const .bottom))
def ballot (n : Nat) : Ground := .binary .pair (cipher n) (ballotTail n)

/-- Key, ciphertext, proof, and a one-candidate tuple are simultaneously public. -/
def published (n : Nat) : Frame {n} 4 :=
  ⟨fun i => if i.val = 0 then key n else if i.val = 1 then cipher n
    else if i.val = 2 then proof n else ballot n⟩

theorem published_protected (n : Nat) : ∀ i, ((published n).value i).nonceSafe {n} = true := by
  intro i
  dsimp [published]
  split_ifs <;> simp [key, cipher, proof, ballot, ballotTail, Term.nonceSafe]

/-- Quantifies over every public recipe, including arbitrary handle duplication. -/
theorem published_nonce_not_deducible (n : Nat) (r : Recipe 4) (hr : r.Public {n}) :
    ¬ EqE ((published n).eval r) (.name n) :=
  (published n).nonce_not_deducible (published_protected n) r hr (by simp)

def selectCipher : Recipe 4 := .unary .fst (.var ⟨3, by decide⟩)

theorem public_ballot_projection (n : Nat) : selectCipher.Public {n} ∧
    EqE ((published n).eval selectCipher) (cipher n) :=
  ⟨trivial, (RootStep.fst (cipher n) (ballotTail n)).to_modulo.sound⟩

def decryptBit (n : Nat) : Recipe 4 := .binary .dec (.name (n + 1)) (.var ⟨1, by decide⟩)

theorem public_decryption_works (n : Nat) : (decryptBit n).Public {n} ∧
    EqE ((published n).eval (decryptBit n)) (.const .one) := by
  refine ⟨?_, (RootStep.decrypt (.name (n + 1)) (.name n) (.const .one)).to_modulo.sound⟩
  simp [decryptBit, Term.Public]

theorem public_recipe_restriction_required (n : Nat) :
    ¬ (Term.name n : Recipe 4).Public {n} ∧
      EqE ((published n).eval (.name n)) (.name n) := by
  exact ⟨by simp [Term.Public], .refl _⟩

/-- Dropping the frame invariant permits a public handle to expose the nonce. -/
theorem unsafe_frame_leaks (n : Nat) :
    let φ : Frame {n} 1 := ⟨fun _ => .name n⟩
    let r : Recipe 1 := .var ⟨0, by decide⟩
    r.Public {n} ∧ EqE (φ.eval r) (.name n) ∧ (φ.value ⟨0, by decide⟩).nonceSafe {n} = false := by
  exact ⟨trivial, .refl _, by simp [Term.nonceSafe]⟩

/-- Encryption randomness is protected; plaintext cannot be treated the same way. -/
theorem plaintext_leak_rejected (n : Nat) :
    let t : Ground := .binary .dec (.name (n + 1))
      (.ternary .penc (key n) (.name (n + 2)) (.name n))
    EqE t (.name n) ∧ t.nonceSafe {n} = false := by
  exact ⟨(RootStep.decrypt (.name (n + 1)) (.name (n + 2)) (.name n)).to_modulo.sound,
    by simp [key, Term.nonceSafe]⟩

theorem full_E_invariance_refuted (n : Nat) :
    let a : Ground := .const .one
    let b : Ground := .unary .fst (.binary .pair a (.name n))
    EqE a b ∧ a.nonceSafe {n} = true ∧ b.nonceSafe {n} = false := by
  exact ⟨(RootStep.fst (.const .one) (.name n)).to_modulo.sound.symm,
    rfl, by simp [Term.nonceSafe]⟩

end ExplainableCrypto.Helios.Symbolic.NonceProtectionSPOT
