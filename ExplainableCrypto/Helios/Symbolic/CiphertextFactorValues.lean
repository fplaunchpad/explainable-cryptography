import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A ciphertext E-value under the specified semantic key. -/
def CiphertextValue (key t : Term V) : Prop := ∃ r m, EqE t (.ternary .penc key r m)

/-- Every representative of every outer E0 factor has a ciphertext E-value.
This does not require literal ciphertext factor shapes or normal inputs. -/
def CiphertextFactors (key t : Term V) : Prop :=
  ∀ a : Term V, a.baseClass ∈ t.mulFactors → CiphertextValue key a

theorem CiphertextValue.pre_eq {key a b : Term V} (h : CiphertextValue key b)
    (he : EqE a b) : CiphertextValue key a := by
  obtain ⟨r, m, hb⟩ := h
  exact ⟨r, m, he.trans hb⟩

/-- The factor property is sufficient for a ciphertext E-value by structural folding. -/
theorem ciphertext_value_of_factors (key t : Term V) :
    CiphertextFactors key t → CiphertextValue key t := by
  induction t with
  | binary f a b ha hb =>
    intro h
    cases f with
    | mul =>
      obtain ⟨r, m, ha⟩ := ha (fun x hx => h x (Multiset.mem_add.mpr (Or.inl hx)))
      obtain ⟨s, n, hb⟩ := hb (fun x hx => h x (Multiset.mem_add.mpr (Or.inr hx)))
      exact ⟨.binary .compose r s, .binary .add m n,
        (EqE.binary .mul ha hb).trans (RootStep.homomorphic key r s m n).sound⟩
    | _ => exact h _ (by simp [Term.mulFactors])
  | _ => intro h; exact h _ (by simp [Term.mulFactors])

namespace CiphertextFactors

theorem of_base {key a b : Term V} (h : CiphertextFactors key b) (he : BaseEq a b) :
    CiphertextFactors key a := by
  intro t ht
  exact h t (he.mul_factors ▸ ht)

theorem penc_of_key_eq {key k : Term V} (hk : EqE k key) (r m : Term V) :
    CiphertextFactors key (.ternary .penc k r m) := by
  intro a ha
  have hc : a.baseClass = (Term.ternary .penc k r m).baseClass := by
    simpa only [Term.mulFactors, Multiset.mem_singleton] using ha
  exact ⟨r, m, ((baseClass_eq_iff _ _).mp hc).sound.trans
    (.ternary .penc hk (.refl _) (.refl _))⟩

/-- Reverse a single-factor reduction, including expansion into several factors. -/
theorem before_factor_step {key source target : Term V} (h : CiphertextFactors key target)
    (hs : FactorStep source target) : CiphertextFactors key source := by
  obtain ⟨a, b, rest, _, hab, hsource, htarget⟩ := hs
  have hb : CiphertextFactors key b := by
    intro x hx
    apply h x
    rw [htarget]
    exact Multiset.mem_add.mpr (Or.inl hx)
  have ha := (ciphertext_value_of_factors key b hb).pre_eq hab.sound
  intro x hx
  rw [hsource] at hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · have he : x.baseClass = a.baseClass := Multiset.mem_singleton.mp hx
    exact ha.pre_eq ((baseClass_eq_iff _ _).mp he).sound
  · apply h x
    rw [htarget]
    exact Multiset.mem_add.mpr (Or.inr hx)

/-- Reverse E7: the combined ciphertext's key value determines both input key values. -/
theorem before_fusion {key source target : Term V} (h : CiphertextFactors key target)
    (hs : OuterFusion source target) : CiphertextFactors key source := by
  obtain ⟨_, _, rest, ⟨k, r, s, m, n, rfl, rfl⟩, hsource, htarget⟩ := hs
  have hout : CiphertextValue key (combinedCiphertext k r s m n) := by
    apply h
    rw [htarget]
    simp
  obtain ⟨_, _, hout⟩ := hout
  have hk : EqE k key := ((EqE.penc_iff _ _ _ _ _ _).mp hout).1
  intro x hx
  rw [hsource] at hx
  rcases Multiset.mem_add.mp hx with hx | hx
  · simp only [ciphertextPairFactors, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hx
    rcases hx with hx | hx
    · exact ⟨r, m, ((baseClass_eq_iff _ _).mp hx).sound.trans
        (.ternary .penc hk (.refl _) (.refl _))⟩
    · exact ⟨s, n, ((baseClass_eq_iff _ _).mp hx).sound.trans
        (.ternary .penc hk (.refl _) (.refl _))⟩
  · apply h x
    rw [htarget]
    exact Multiset.mem_add.mpr (Or.inr hx)

theorem before_step {key source target : Term V} (h : CiphertextFactors key target)
    (hs : ModuloStep source target) : CiphertextFactors key source :=
  hs.factor_cases.elim h.before_fusion h.before_factor_step

end CiphertextFactors

theorem ReducesModulo.ciphertext_factors_before {key source target : Term V}
    (h : ReducesModulo source target) : CiphertextFactors key target → CiphertextFactors key source := by
  induction h with
  | base hb => exact fun h => h.of_base hb
  | head hs _ ih => exact fun h => (ih h).before_step hs

/-- Full-E ciphertext equality forces the property for every original factor.
Confluence and passive ciphertext paths supply the common descendant's key value. -/
theorem EqE.ciphertext_factors {t key r m : Term V}
    (h : EqE t (.ternary .penc key r m)) : CiphertextFactors key t := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  obtain ⟨k, r', m', hw, hk, _, _⟩ := hr.penc_components
  exact hl.ciphertext_factors_before
    ((CiphertextFactors.penc_of_key_eq hk.sound.symm r' m').of_base hw)

/-- Characterization in terms of full-E factor values, not literal factor syntax. -/
theorem ciphertext_value_iff_factors (key t : Term V) :
    CiphertextValue key t ↔ CiphertextFactors key t := by
  constructor
  · rintro ⟨r, m, h⟩
    exact h.ciphertext_factors
  · exact ciphertext_value_of_factors key t

end ExplainableCrypto.Helios.Symbolic
