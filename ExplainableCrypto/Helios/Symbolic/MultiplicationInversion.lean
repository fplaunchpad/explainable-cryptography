import ExplainableCrypto.Helios.Symbolic.CiphertextFactorValues

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A product has a ciphertext E-value under a key exactly when both operands do. -/
theorem CiphertextValue.mul_iff (key a b : Term V) :
    CiphertextValue key (.binary .mul a b) ↔ CiphertextValue key a ∧ CiphertextValue key b := by
  constructor
  · intro h
    have hf := (ciphertext_value_iff_factors _ _).mp h
    exact ⟨ciphertext_value_of_factors key a (fun x hx => hf x (Multiset.mem_add.mpr (Or.inl hx))),
      ciphertext_value_of_factors key b (fun x hx => hf x (Multiset.mem_add.mpr (Or.inr hx)))⟩
  · rintro ⟨⟨r, m, ha⟩, ⟨s, n, hb⟩⟩
    exact ⟨.binary .compose r s, .binary .add m n,
      (EqE.binary .mul ha hb).trans (RootStep.homomorphic key r s m n).sound⟩

/-- Full-E multiplication inversion retains both ciphertext origins and their exact
combined nonce/message values. Neither inputs nor target components must be normal. -/
theorem EqE.mul_penc_inversion {a b key nonce message : Term V}
    (h : EqE (.binary .mul a b) (.ternary .penc key nonce message)) :
    ∃ r s m n, EqE a (.ternary .penc key r m) ∧ EqE b (.ternary .penc key s n) ∧
      EqE (.binary .compose r s) nonce ∧ EqE (.binary .add m n) message := by
  obtain ⟨⟨r, m, ha⟩, ⟨s, n, hb⟩⟩ := (CiphertextValue.mul_iff key a b).mp ⟨nonce, message, h⟩
  have hc := ((EqE.binary .mul ha hb).trans (RootStep.homomorphic key r s m n).sound).symm.trans h
  have hcomponents := (EqE.penc_iff _ _ _ _ _ _).mp hc
  exact ⟨r, s, m, n, ha, hb, hcomponents.2.1, hcomponents.2.2⟩

theorem EqE.mul_penc_iff (a b key nonce message : Term V) :
    EqE (.binary .mul a b) (.ternary .penc key nonce message) ↔
      ∃ r s m n, EqE a (.ternary .penc key r m) ∧ EqE b (.ternary .penc key s n) ∧
        EqE (.binary .compose r s) nonce ∧ EqE (.binary .add m n) message := by
  constructor
  · exact EqE.mul_penc_inversion
  · rintro ⟨r, s, m, n, ha, hb, hr, hm⟩
    exact ((EqE.binary .mul ha hb).trans (RootStep.homomorphic key r s m n).sound).trans
      (.ternary .penc (.refl _) hr hm)

/-- A product cannot discard a name factor to obtain a ciphertext. -/
theorem name_factor_not_ciphertext (a key nonce message : Term V) (n : Nat) :
    ¬ EqE (.binary .mul a (.name n)) (.ternary .penc key nonce message) := by
  intro h
  obtain ⟨_, _, _, _, _, hb, _⟩ := h.mul_penc_inversion
  obtain ⟨_, _, _, he, _⟩ := hb.symm.penc_irreducible_shape (name_irreducible n)
  cases he

/-- Fusion cannot turn genuinely different key values into one common key. -/
theorem unequal_keys_product_not_ciphertext (k l r s m n key nonce message : Term V)
    (hne : ¬ EqE k l) :
    ¬ EqE (.binary .mul (.ternary .penc k r m) (.ternary .penc l s n))
      (.ternary .penc key nonce message) := by
  intro h
  obtain ⟨_, _, _, _, ha, hb, _⟩ := h.mul_penc_inversion
  have hk := ((EqE.penc_iff _ _ _ _ _ _).mp ha).1
  have hl := ((EqE.penc_iff _ _ _ _ _ _).mp hb).1
  exact hne (hk.trans hl.symm)

end ExplainableCrypto.Helios.Symbolic
