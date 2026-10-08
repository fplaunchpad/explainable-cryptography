import ExplainableCrypto.Helios.Symbolic.FullStructure

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Every step replaces one composition factor by a nonempty factor bag. -/
theorem ModuloStep.compose_card_le {a b : Term V} (h : ModuloStep a b) :
    a.composeFactors.card ≤ b.composeFactors.card := by
  obtain ⟨x, y, rest, _, _, ha, hb⟩ := h.compose_factor
  have hy : 0 < y.composeFactors.card := Multiset.card_pos.mpr y.composeFactors_nonempty
  rw [ha, hb, Multiset.card_add, Multiset.card_add, Multiset.card_singleton]
  omega

theorem ReducesModulo.compose_card_le {a b : Term V} (h : ReducesModulo a b) :
    a.composeFactors.card ≤ b.composeFactors.card := by
  induction h with
  | base he => exact Nat.le_of_eq (congrArg Multiset.card he.compose_factors)
  | head hs _ ih => exact hs.compose_card_le.trans ih

theorem Term.compose_shape_of_card {t : Term V} (h : 2 ≤ t.composeFactors.card) :
    ∃ a b, t = .binary .compose a b := by
  cases t with
  | binary f a b => cases f <;> simp_all [Term.composeFactors]
  | _ => simp_all [Term.composeFactors]

/-- Literal composition shape persists on actual paths, including E0 endpoints. -/
theorem ReducesModulo.compose_shape {a b t : Term V} (h : ReducesModulo (.binary .compose a b) t) :
    ∃ x y, t = .binary .compose x y := by
  have ha : 0 < a.composeFactors.card := Multiset.card_pos.mpr a.composeFactors_nonempty
  have hb : 0 < b.composeFactors.card := Multiset.card_pos.mpr b.composeFactors_nonempty
  have hc := h.compose_card_le
  simp only [Term.composeFactors, Multiset.card_add] at hc
  exact Term.compose_shape_of_card (by omega)

/-- Full-E literal shape additionally requires a normal target. -/
theorem EqE.compose_irreducible_shape {a b t : Term V}
    (h : EqE (.binary .compose a b) t) (ht : Irreducible t) :
    ∃ x y, t = .binary .compose x y := by
  obtain ⟨w, hl, hr⟩ := (eqE_iff_join _ _).mp h
  have he := ht.reducesModulo hr
  have hc := hl.compose_card_le
  rw [← he.compose_factors] at hc
  have ha : 0 < a.composeFactors.card := Multiset.card_pos.mpr a.composeFactors_nonempty
  have hb : 0 < b.composeFactors.card := Multiset.card_pos.mpr b.composeFactors_nonempty
  simp only [Term.composeFactors, Multiset.card_add] at hc
  exact Term.compose_shape_of_card (by omega)

end ExplainableCrypto.Helios.Symbolic
