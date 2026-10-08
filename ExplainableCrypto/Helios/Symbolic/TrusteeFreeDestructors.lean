import ExplainableCrypto.Helios.Symbolic.TrusteeFreeMultiplication

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {secret : Nat}

/-- Reflection requires a stuck projection; a successful selector can erase data. -/
theorem TrusteeFreeValue.projection_of_no_pair (f : Unary) (hf : f = .fst ∨ f = .snd)
    (a : Term V) (hn : ∀ x y, ¬ EqE a (.binary .pair x y))
    (h : TrusteeFreeValue secret (.unary f a)) : TrusteeFreeValue secret a := by
  obtain ⟨u, he, hi, hfree⟩ := h.normal_rep
  obtain ⟨a', rfl, ha⟩ := projection_normal_shape_of_no_pair f hf a hn hi he
  exact ⟨a', ha, hfree⟩

theorem TrusteeFreeValue.decryption_of_no_match (a b : Term V)
    (hn : ∀ p, ¬ DecryptionMatch a b p)
    (h : TrusteeFreeValue secret (.binary .dec a b)) :
    TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b := by
  obtain ⟨u, he, hi, hf⟩ := h.normal_rep
  obtain ⟨a', b', rfl, ha, hb⟩ := decryption_normal_shape_of_no_match a b hn hi he
  exact ⟨⟨a', ha, hf.1⟩, ⟨b', hb, hf.2.1⟩⟩

theorem TrusteeFreeValue.check_of_no_match (a b c : Term V)
    (hn : ¬ ProofCheckMatch a b c)
    (h : TrusteeFreeValue secret (.ternary .checkspk a b c)) :
    TrusteeFreeValue secret a ∧ TrusteeFreeValue secret b ∧ TrusteeFreeValue secret c := by
  obtain ⟨u, he, hi, hf⟩ := h.normal_rep
  obtain ⟨a', b', c', rfl, ha, hb, hc⟩ := proof_check_normal_shape_of_no_match a b c hn hi he
  exact ⟨⟨a', ha, hf.1⟩, ⟨b', hb, hf.2.1⟩, ⟨c', hc, hf.2.2⟩⟩

end ExplainableCrypto.Helios.Symbolic
