import ExplainableCrypto.Helios.Symbolic.PairSelectionCases

namespace ExplainableCrypto.Helios.Symbolic

/-- A rule replaces its selected input bag by one output, retaining the exact remainder. -/
def BagFusion {α : Type} (rule : Multiset α → α → Prop) (source target : Multiset α) : Prop :=
  ∃ inputs output rest, rule inputs output ∧ source = inputs + rest ∧ target = {output} + rest

private theorem bag_shuffle {α : Type} (a b c : Multiset α) : a + (b + c) = b + (a + c) := by
  rw [← Multiset.add_assoc, Multiset.add_comm a b, Multiset.add_assoc]

private theorem bag_pair_rotate {α : Type} (a b c : α) (rest : Multiset α) :
    {a, b} + ({c} + rest) = {b, c} + ({a} + rest) := by
  simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
  rw [Multiset.cons_swap a b, Multiset.cons_swap a c]

/-- A conditional combinatorial theorem. Protocol-specific rule laws must be supplied. -/
theorem bag_fusion_diamond {α : Type} (rule : Multiset α → α → Prop)
    (hrank : ∀ p x, rule p x → p.card = 2)
    (hdet : ∀ p x y, rule p x → rule p y → x = y)
    (hassoc : ∀ a b c x y, rule {a, b} x → rule {b, c} y →
      ∃ z, rule {x, c} z ∧ rule {a, y} z)
    {source u v : Multiset α} (hu : BagFusion rule source u) (hv : BagFusion rule source v) :
    u = v ∨ ∃ w, BagFusion rule u w ∧ BagFusion rule v w := by
  obtain ⟨p, x, rp, hp, hsp, hu⟩ := hu
  obtain ⟨q, y, rq, hq, hsq, hv⟩ := hv
  have hp_le : p ≤ source := by rw [hsp]; exact Multiset.le_add_right _ _
  have hq_le : q ≤ source := by rw [hsq]; exact Multiset.le_add_right _ _
  rcases pair_selection_cases source p q hp_le hq_le (hrank p x hp) (hrank q y hq) with
    he | ⟨b, a, c, rest, rfl, rfl, hs⟩ | ⟨rest, hs⟩
  · subst q
    have hr : rp = rq := Multiset.add_right_inj.mp (hsp.symm.trans hsq)
    exact Or.inl (by rw [hu, hv, hr, hdet _ _ _ hp hq])
  · obtain ⟨z, hz₁, hz₂⟩ := hassoc a b c x y hp hq
    have hrp : rp = {c} + rest := Multiset.add_right_inj.mp (hsp.symm.trans hs)
    have hrq : rq = {a} + rest := Multiset.add_right_inj.mp
      (hsq.symm.trans (hs.trans (bag_pair_rotate _ _ _ rest)))
    refine Or.inr ⟨{z} + rest, ⟨{x, c}, z, rest, hz₁, ?_, rfl⟩,
      ⟨{a, y}, z, rest, hz₂, ?_, rfl⟩⟩
    · rw [hu, hrp]
      simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
    · rw [hv, hrq]
      simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add]
      exact Multiset.cons_swap _ _ _
  · have hrp : rp = q + rest := Multiset.add_right_inj.mp (hsp.symm.trans hs)
    have hrq : rq = p + rest := Multiset.add_right_inj.mp
      (hsq.symm.trans (hs.trans (bag_shuffle _ _ _)))
    refine Or.inr ⟨{y} + ({x} + rest),
      ⟨q, y, {x} + rest, hq, ?_, rfl⟩,
      ⟨p, x, {y} + rest, hp, ?_, bag_shuffle _ _ _⟩⟩
    · rw [hu, hrp]
      exact bag_shuffle _ _ _
    · rw [hv, hrq]
      exact bag_shuffle _ _ _

end ExplainableCrypto.Helios.Symbolic
