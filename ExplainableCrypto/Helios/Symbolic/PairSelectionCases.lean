import Mathlib.Data.Multiset.UnionInter
import Mathlib.Data.Multiset.Dedup
import Lean.Elab.Tactic.Omega

namespace ExplainableCrypto.Helios.Symbolic

/-- A classification of selected bags, not recovered syntax-position identities.
Repeated values retain multiplicity. Several valid realizations may coexist. -/
def PairSelectionCases {α : Type} (source p q : Multiset α) : Prop :=
  p = q ∨
    (∃ shared a b rest, p = {a, shared} ∧ q = {shared, b} ∧
      source = {a, shared} + ({b} + rest)) ∨
    (∃ rest, source = p + (q + rest))

/-- Every two size-two selections from one source admit an identical, shared,
or disjoint bag decomposition. No distinct-value premise is needed. -/
theorem pair_selection_cases {α : Type} (source p q : Multiset α)
    (hp : p ≤ source) (hq : q ≤ source) (hp2 : p.card = 2) (hq2 : q.card = 2) :
    PairSelectionCases source p q := by
  classical
  obtain ⟨rest, hsource⟩ := Multiset.le_iff_exists_add.mp (Multiset.union_le hp hq)
  have hbound : (p ∩ q).card ≤ 2 := by
    simpa only [hp2] using Multiset.card_le_card (Multiset.inter_le_left (s := p) (t := q))
  have hcases : (p ∩ q).card = 0 ∨ (p ∩ q).card = 1 ∨ (p ∩ q).card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have hshared : p ∩ q = 0 := Multiset.card_eq_zero.mp hzero
    have hunion : p ∪ q = p + q := by
      simpa only [hshared, Multiset.add_zero] using Multiset.union_add_inter p q
    exact Or.inr (Or.inr ⟨rest, by rw [hsource, hunion, Multiset.add_assoc]⟩)
  · obtain ⟨shared, hshared⟩ := Multiset.card_eq_one.mp hone
    obtain ⟨left, hleft⟩ := Multiset.le_iff_exists_add.mp (Multiset.inter_le_left (s := p) (t := q))
    obtain ⟨right, hright⟩ := Multiset.le_iff_exists_add.mp (Multiset.inter_le_right (s := p) (t := q))
    have hlcard : left.card = 1 := by
      have hc := congrArg Multiset.card hleft
      simp only [Multiset.card_add, hone] at hc
      omega
    have hrcard : right.card = 1 := by
      have hc := congrArg Multiset.card hright
      simp only [Multiset.card_add, hone] at hc
      omega
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp hlcard
    obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hrcard
    have hp' : p = {a, shared} := by
      rw [hleft, hshared, ha]
      simpa only [Multiset.singleton_add, Multiset.insert_eq_cons] using Multiset.pair_comm shared a
    have hq' : q = {shared, b} := by
      rw [hright, hshared, hb]
      simp only [Multiset.singleton_add, Multiset.insert_eq_cons]
    have hunion : p ∪ q = p + {b} := by
      have hright' : q = p ∩ q + {b} := by simpa only [hb] using hright
      have hu := (Multiset.union_add_inter p q).trans (congrArg (fun x => p + x) hright')
      ext x
      have hc := congrArg (Multiset.count x) hu
      simp only [Multiset.count_add] at hc ⊢
      omega
    exact Or.inr (Or.inl ⟨shared, a, b, rest, hp', hq', by
      rw [hsource, hunion, hp', Multiset.add_assoc]⟩)
  · have hp' : p ∩ q = p := Multiset.eq_of_le_of_card_le Multiset.inter_le_left (by omega)
    have hq' : p ∩ q = q := Multiset.eq_of_le_of_card_le Multiset.inter_le_right (by omega)
    exact Or.inl (hp'.symm.trans hq')

namespace PairSelectionSPOT

/-- Repeated identical selections still have cardinality two. -/
theorem identical_repeated_pair :
    PairSelectionCases ({0, 0, 1} : Multiset Nat) {0, 0} {0, 0} ∧
      (({0, 0} : Multiset Nat) ∩ {0, 0}).card = 2 :=
  ⟨pair_selection_cases _ _ _ (by decide) (by decide) (by decide) (by decide), by decide⟩

/-- One repeated value and one distinct value give the three-occurrence case. -/
theorem shared_repeated_pair :
    PairSelectionCases ({0, 0, 1} : Multiset Nat) {0, 0} {0, 1} ∧
      (({0, 0} : Multiset Nat) ∩ {0, 1}).card = 1 ∧
      ({0, 0, 1} : Multiset Nat) = {0, 0} + {1} :=
  ⟨pair_selection_cases _ _ _ (by decide) (by decide) (by decide) (by decide), by decide, by decide⟩

/-- Disjoint repeated pairs need four occurrences. -/
theorem disjoint_repeated_pairs :
    PairSelectionCases ({0, 0, 1, 1} : Multiset Nat) {0, 0} {1, 1} ∧
      (({0, 0} : Multiset Nat) ∩ {1, 1}).card = 0 ∧
      ({0, 0, 1, 1} : Multiset Nat) = {0, 0} + {1, 1} :=
  ⟨pair_selection_cases _ _ _ (by decide) (by decide) (by decide) (by decide), by decide, by decide⟩

/-- Retain the gate's smallest deduplication failure. -/
theorem deduplication_loses_an_occurrence :
    ({0, 0} : Multiset Nat).card = 2 ∧ (Multiset.dedup ({0, 0} : Multiset Nat)).card ≠ 2 := by
  decide

end PairSelectionSPOT
end ExplainableCrypto.Helios.Symbolic
