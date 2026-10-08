import ExplainableCrypto.Helios.Symbolic.StuckDestructorOrigins

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

private theorem reaches_normal {a b : Term V} (he : EqE a b) (hb : Irreducible b) : ReducesModulo a b := by
  obtain ⟨w, ha, hw⟩ := (eqE_iff_join _ _).mp he
  exact ha.post_base (hb.reducesModulo hw).symm

private theorem partial_normal {a b : Term V} (ha : Irreducible a) (hb : Irreducible b) :
    Irreducible (.binary .partialDecrypt a b) := by
  intro t ht
  rcases ht.passive_binary_cases (Or.inr rfl) with ⟨_, hs, _⟩ | ⟨_, hs, _⟩
  · exact ha _ hs
  · exact hb _ hs

/-- Semantic matching data produces an actual reachable E5/E6 match. The output
may be a reduced representative of the supplied plaintext. -/
theorem DecryptionMatch.exists_of_values {a b k nonce p : Term V}
    (hb : EqE b (keyCiphertext k nonce p))
    (ha : EqE a k ∨ EqE a (.binary .partialDecrypt k b)) :
    ∃ m, DecryptionMatch a b m := by
  obtain ⟨t, hpath, ht⟩ := exists_normal_form b
  have hbt := hpath.to_modulo
  obtain ⟨key', nonce', p', rfl, hk, _⟩ := (hb.symm.trans hbt.sound).penc_irreducible_shape ht
  have hkey := ht.context_hole (.ternaryFirst .penc .hole nonce' p')
  obtain ⟨k', rfl, hkk⟩ := hk.pk_irreducible_shape hkey
  have hkn := hkey.context_hole (.unary .pk .hole)
  refine ⟨p', k', nonce', ?_, hbt⟩
  rcases ha with ha | ha
  · exact Or.inl (reaches_normal (ha.trans hkk) hkn)
  · exact Or.inr (reaches_normal
      (ha.trans (.binary .partialDecrypt hkk hbt.sound)) (partial_normal hkn ht))

/-- Every reachable match has ciphertext and direct/partial-key E-values. This
characterization retains the entire supplied ciphertext in the E6 binding. -/
theorem DecryptionMatch.exists_iff_values (a b : Term V) :
    (∃ m, DecryptionMatch a b m) ↔
      ∃ k nonce p, EqE b (keyCiphertext k nonce p) ∧
        (EqE a k ∨ EqE a (.binary .partialDecrypt k b)) := by
  constructor
  · rintro ⟨m, k, nonce, hk, hb⟩
    refine ⟨k, nonce, m, hb.sound, ?_⟩
    rcases hk with hk | hk
    · exact Or.inl hk.sound
    · exact Or.inr (hk.sound.trans (.binary .partialDecrypt (.refl _) hb.sound.symm))
  · rintro ⟨k, nonce, p, hb, ha⟩
    exact DecryptionMatch.exists_of_values hb ha

/-- A partial-decryption constructor can also be an ordinary E5 secret key.
Both alternatives must be retained in this unsorted symbolic model. -/
theorem DecryptionMatch.partial_key_iff (a binding b key nonce p : Term V)
    (hb : EqE b (.ternary .penc key nonce p)) :
    (∃ m, DecryptionMatch (.binary .partialDecrypt a binding) b m) ↔
      EqE key (.unary .pk (.binary .partialDecrypt a binding)) ∨
        (EqE key (.unary .pk a) ∧ EqE binding b) := by
  constructor
  · rintro ⟨m, k, r, hk, hc⟩
    have hkey := ((EqE.penc_iff _ _ _ _ _ _).mp (hb.symm.trans hc.sound)).1
    rcases hk with hk | hk
    · exact Or.inl (hkey.trans (.unary .pk hk.sound.symm))
    · have hparts := (EqE.partialDecrypt_iff _ _ _ _).mp hk.sound
      exact Or.inr ⟨hkey.trans (.unary .pk hparts.1.symm), hparts.2.trans hc.sound.symm⟩
  · intro h
    rcases h with h | ⟨hkey, hbinding⟩
    · exact DecryptionMatch.exists_of_values
        (hb.trans (.ternary .penc h (.refl _) (.refl _))) (Or.inl (.refl _))
    · exact DecryptionMatch.exists_of_values
        (hb.trans (.ternary .penc hkey (.refl _) (.refl _)))
        (Or.inr (.binary .partialDecrypt (.refl _) hbinding))

end ExplainableCrypto.Helios.Symbolic
