import ExplainableCrypto.Helios.Symbolic.MultiplicationInversion
import ExplainableCrypto.Helios.Symbolic.ProjectionPaths

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A product has at least two factors until fusion gives a ciphertext value.
This is a path invariant, not an E0 literal-shape classifier for arbitrary terms. -/
def ProductEndpoint (t : Term V) : Prop := 2 ≤ t.mulFactors.card ∨ ∃ key, CiphertextValue key t

private theorem factor_card_pos (t : Term V) : 0 < t.mulFactors.card :=
  Multiset.card_pos.mpr t.mulFactors_nonempty

theorem ProductEndpoint.mul (a b : Term V) : ProductEndpoint (.binary .mul a b) := by
  left
  have ha := factor_card_pos a
  have hb := factor_card_pos b
  simp only [Term.mulFactors, Multiset.card_add]
  omega

theorem ProductEndpoint.of_base {a b : Term V} (h : ProductEndpoint a) (he : BaseEq a b) :
    ProductEndpoint b := by
  rcases h with h | ⟨key, h⟩
  · exact Or.inl (he.mul_factors ▸ h)
  · exact Or.inr ⟨key, h.pre_eq he.sound.symm⟩

theorem ProductEndpoint.step {a b : Term V} (h : ProductEndpoint a) (hs : ModuloStep a b) :
    ProductEndpoint b := by
  rcases h with hcard | ⟨key, hv⟩
  · rcases hs.factor_cases with hf | hi
    · obtain ⟨_, _, rest, ⟨k, r, s, m, n, rfl, rfl⟩, _, hb⟩ := hf
      by_cases hz : rest = 0
      · subst rest
        have he : BaseEq b (combinedCiphertext k r s m n) :=
          (baseEq_iff_mulFactors _ _).mpr (by simpa [Term.mulFactors] using hb)
        exact Or.inr ⟨k, .binary .compose r s, .binary .add m n, he.sound⟩
      · left
        have hrest : 0 < rest.card := Multiset.card_pos.mpr hz
        rw [hb, Multiset.card_add, Multiset.card_singleton]
        omega
    · obtain ⟨x, y, rest, _, _, ha, hb⟩ := hi
      have hy := factor_card_pos y
      rw [ha, Multiset.card_add, Multiset.card_singleton] at hcard
      left
      rw [hb, Multiset.card_add]
      omega
  · exact Or.inr ⟨key, hv.pre_eq hs.sound.symm⟩

theorem ProductEndpoint.reduces {a b : Term V} (h : ProductEndpoint a) (hs : ReducesModulo a b) :
    ProductEndpoint b := by
  induction hs with
  | base he => exact h.of_base he
  | head hstep _ ih => exact ih (h.step hstep)

theorem ReducesModulo.mul_endpoint {a b t : Term V} (h : ReducesModulo (.binary .mul a b) t) :
    ProductEndpoint t := (ProductEndpoint.mul a b).reduces h

/-- Every normal E-value of a product has a multiplication or ciphertext head. -/
theorem EqE.mul_irreducible_shape {a b t : Term V}
    (h : EqE (.binary .mul a b) t) (ht : Irreducible t) :
    (∃ x y, t = .binary .mul x y) ∨ (∃ k r m, t = .ternary .penc k r m) := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  have he := ht.reducesModulo hr
  rcases hl.mul_endpoint.of_base he.symm with hcard | ⟨k, r, m, hc⟩
  · left
    cases t with
    | binary f x y => cases f <;> simp_all [Term.mulFactors]
    | _ => simp_all [Term.mulFactors]
  · obtain ⟨k', r', m', he, _⟩ := hc.symm.penc_irreducible_shape ht
    exact Or.inr ⟨k', r', m', he⟩

/-- Pair and partial-decryption targets may have arbitrary reducible components. -/
theorem mul_not_eqE_passive_binary (a b x y : Term V) (f : Binary)
    (hf : f = .pair ∨ f = .partialDecrypt) :
    ¬ EqE (.binary .mul a b) (.binary f x y) := by
  intro h
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨x', y', hw, _⟩ := hr.passive_binary_components hf
  rcases hl.mul_endpoint.of_base hw with hcard | ⟨k, r, m, hc⟩
  · rcases hf with rfl | rfl <;> simp [Term.mulFactors] at hcard
  · exact penc_not_eqE_passive_binary f hf k r m x' y' hc.symm

theorem mul_not_eqE_spk (a b k r m c : Term V) :
    ¬ EqE (.binary .mul a b) (.spk k r m c) := by
  intro h
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨k', r', m', c', hw, _⟩ := hr.spk_components
  rcases hl.mul_endpoint.of_base hw with hcard | ⟨key, nonce, message, hc⟩
  · simp [Term.mulFactors] at hcard
  · exact penc_not_eqE_spk key nonce message k' r' m' c' hc.symm

theorem mul_not_eqE_pk (a b k : Term V) : ¬ EqE (.binary .mul a b) (.unary .pk k) := by
  intro h
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨k', hw, _⟩ := hr.pk_components
  rcases hl.mul_endpoint.of_base hw with hcard | ⟨key, nonce, message, hc⟩
  · simp [Term.mulFactors] at hcard
  · exact pk_not_eqE_penc k' key nonce message hc

theorem mul_not_eqE_constant (a b : Term V) (c : Constant) :
    ¬ EqE (.binary .mul a b) (.const c) := by
  intro h
  rcases h.mul_irreducible_shape (constant_irreducible c) with ⟨x, y, he⟩ | ⟨k, r, m, he⟩ <;> cases he

theorem mul_not_eqE_name (a b : Term V) (n : Nat) :
    ¬ EqE (.binary .mul a b) (.name n) := by
  intro h
  rcases h.mul_irreducible_shape (name_irreducible n) with ⟨x, y, he⟩ | ⟨k, r, m, he⟩ <;> cases he

theorem mul_not_eqE_var (a b : Term V) (v : V) :
    ¬ EqE (.binary .mul a b) (.var v) := by
  intro h
  rcases h.mul_irreducible_shape (var_irreducible v) with ⟨x, y, he⟩ | ⟨k, r, m, he⟩ <;> cases he

end ExplainableCrypto.Helios.Symbolic
