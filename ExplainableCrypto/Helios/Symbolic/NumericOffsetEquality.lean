import ExplainableCrypto.Helios.Symbolic.NumericAdditionInversion

namespace ExplainableCrypto.Helios.Symbolic
variable {α V : Type}

/-- Once a numeric summand is present, equality retains the atom bag and total
numeric value, but cannot distinguish absent numeric content from present zero. -/
theorem AddSummary.combine_number_eq_iff (a b : AddSummary α) (k : Nat) :
    a.combine (.number k) = b.combine (.number k) ↔
      a.atoms = b.atoms ∧ a.numeric.getD 0 = b.numeric.getD 0 := by
  rcases a with ⟨aa, an⟩
  rcases b with ⟨ba, bn⟩
  cases an <;> cases bn <;>
    simp [AddSummary.combine, AddSummary.number, numericAdd, Nat.add_comm, eq_comm]

theorem AddSummary.numeric_offset_eq_iff (a b : AddSummary α) (k l : Nat) :
    a.combine (.number k) = b.combine (.number k) ↔
      a.combine (.number l) = b.combine (.number l) :=
  (a.combine_number_eq_iff b k).trans (a.combine_number_eq_iff b l).symm

/-- Exact E0 cancellation with a common numeric offset, rather than reflection
back to the unpadded payloads. The payloads may be arbitrary open terms. -/
theorem BaseEq.add_numeric_offset_iff (p q : Term V) (k l : Nat) :
    BaseEq (.binary .add p (addNumeral k)) (.binary .add q (addNumeral k)) ↔
      BaseEq (.binary .add p (addNumeral l)) (.binary .add q (addNumeral l)) := by
  simp only [baseEq_iff_addSummary, Term.addSummary, addNumeral_summary]
  exact AddSummary.numeric_offset_eq_iff _ _ k l

/-- This local enriched-ciphertext equality is independent of a common numeric
honest contribution. It does not reflect to open vote variables. -/
theorem BaseEq.ciphertext_numeric_offset_iff (key nonce p q : Term V) (k l : Nat) :
    BaseEq (.ternary .penc key nonce (.binary .add p (addNumeral k)))
      (.ternary .penc key nonce (.binary .add q (addNumeral k))) ↔
    BaseEq (.ternary .penc key nonce (.binary .add p (addNumeral l)))
      (.ternary .penc key nonce (.binary .add q (addNumeral l))) := by
  simp only [BaseEq.penc_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (BaseEq.add_numeric_offset_iff p q k l))

theorem BaseEq.zero_padding_after_number (p : Term V) (k : Nat) :
    BaseEq (.binary .add p (addNumeral k))
      (.binary .add (.binary .add p (.const .zero)) (addNumeral k)) := by
  apply (baseEq_iff_addSummary _ _).mpr
  simp [Term.addSummary, addNumeral_summary, AddSummary.combine_assoc]

/-- Full-E offset cancellation also covers reducible payloads. Normal forms
are obtained internally; no raw-normality premise is imposed on the caller. -/
theorem EqE.add_numeric_offset_iff (p q : Term V) (k l : Nat) :
    EqE (.binary .add p (addNumeral k)) (.binary .add q (addNumeral k)) ↔
      EqE (.binary .add p (addNumeral l)) (.binary .add q (addNumeral l)) := by
  obtain ⟨p', hp, hnp⟩ := exists_normal_form p
  obtain ⟨q', hq, hnq⟩ := exists_normal_form q
  have forward (k l : Nat)
      (he : EqE (.binary .add p (addNumeral k)) (.binary .add q (addNumeral k))) :
      EqE (.binary .add p (addNumeral l)) (.binary .add q (addNumeral l)) := by
    have hn := (EqE.binary .add hp.sound (.refl (addNumeral k))).symm.trans
      (he.trans (EqE.binary .add hq.sound (.refl _)))
    have hb := (irreducible_eqE_iff_base (hnp.add (addNumeral_irreducible k))
      (hnq.add (addNumeral_irreducible k))).mp hn
    have hl := (BaseEq.add_numeric_offset_iff p' q' k l).mp hb
    exact (EqE.binary .add hp.sound (.refl _)).trans
      (hl.sound.trans (EqE.binary .add hq.sound (.refl _)).symm)
  exact ⟨forward k l, forward l k⟩

theorem EqE.ciphertext_numeric_offset_iff (key nonce p q : Term V) (k l : Nat) :
    EqE (.ternary .penc key nonce (.binary .add p (addNumeral k)))
      (.ternary .penc key nonce (.binary .add q (addNumeral k))) ↔
    EqE (.ternary .penc key nonce (.binary .add p (addNumeral l)))
      (.ternary .penc key nonce (.binary .add q (addNumeral l))) := by
  simp only [EqE.penc_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (EqE.add_numeric_offset_iff p q k l))

end ExplainableCrypto.Helios.Symbolic
