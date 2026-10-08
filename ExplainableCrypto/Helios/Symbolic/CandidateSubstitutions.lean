import ExplainableCrypto.Helios.Symbolic.NumericAdditionInversion

namespace ExplainableCrypto.Helios.Symbolic
open Historical
variable {V W α : Type} {n : Nat}

private theorem foldl_bit_components (xs : List α) (f : α → Term V) (a : Term V)
    (h : BitValue (xs.foldl (fun acc j => .binary .add acc (f j)) a)) :
    BitValue a ∧ ∀ j ∈ xs, BitValue (f j) := by
  induction xs generalizing a with
  | nil => exact ⟨h, by simp⟩
  | cons j xs ih =>
    obtain ⟨ha, hx⟩ := ih (.binary .add a (f j)) h
    obtain ⟨ha, hj⟩ := ha.add_components
    refine ⟨ha, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hj
    · exact hx k hk

/-- Definition 4 alone forces every component to have a bit value under full E. -/
theorem CandidateValues.component_bit {values : Fin (n + 1) → Term V}
    (h : CandidateValues values) (j : Fin (n + 1)) : BitValue (values j) := by
  have hc := foldl_bit_components (List.finRange n) (fun j => values j.succ) (values 0) h
  rcases j with ⟨j, hj⟩
  cases j with
  | zero => exact hc.1
  | succ j => exact hc.2 ⟨j, by omega⟩ (by simp)

theorem CandidateValues.congr {a b : Fin (n + 1) → Term V}
    (ha : CandidateValues a) (he : ∀ j, EqE (a j) (b j)) : CandidateValues b := by
  have h := foldCandidates_congr .add a b he
  rcases ha with hz | ho
  · exact Or.inl (h.symm.trans hz)
  · exact Or.inr (h.symm.trans ho)

/-- Source candidate substitutions may contain arbitrary E-equivalent representatives. -/
structure CandidateSubstitution (n : Nat) (V : Type) where
  value : Fin (n + 1) → Term V
  valid : CandidateValues value

/-- A literal bit representative includes abstention; validity is still the source sum. -/
structure BitCandidate (n : Nat) where
  bit : Fin (n + 1) → Constant
  isBit : ∀ j, bit j = .zero ∨ bit j = .one
  valid : CandidateValues (V := Empty) (fun j => .const (bit j))

def BitCandidate.values (b : BitCandidate n) : Fin (n + 1) → Term V := fun j => .const (b.bit j)

def BitCandidate.substitution (b : BitCandidate n) : CandidateSubstitution n V :=
  ⟨b.values, candidate_bits_change_variables b.bit b.valid⟩

/-- Every valid candidate substitution has a componentwise E-equal literal bit vector. -/
theorem CandidateSubstitution.bit_representative (c : CandidateSubstitution n V) :
    ∃ b : BitCandidate n, ∀ j, EqE (c.value j) (b.values j) := by
  have hb : ∀ j, ∃ bit : Constant, (bit = .zero ∨ bit = .one) ∧ EqE (c.value j) (.const bit) := by
    intro j
    rcases c.valid.component_bit j with hz | ho
    · exact ⟨.zero, Or.inl rfl, hz⟩
    · exact ⟨.one, Or.inr rfl, ho⟩
  choose bits hbits he using hb
  have hc := c.valid.congr he
  exact ⟨⟨bits, hbits, candidate_bits_change_variables bits hc⟩, he⟩

private theorem foldl_zero (xs : List α) (a : Term V) (ha : BaseEq a (.const .zero)) :
    BaseEq (xs.foldl (fun acc _ => .binary .add acc (.const .zero)) a) (.const .zero) := by
  induction xs generalizing a with
  | nil => exact ha
  | cons j xs ih => exact ih _ ((BaseEq.binary .add ha (.refl _)).trans (.equation .zero_zero))

theorem zero_candidate_values : CandidateValues (V := V) (n := n) (fun _ => .const .zero) :=
  Or.inl (foldl_zero (List.finRange n) (.const .zero) (.refl _)).sound

def BitCandidate.abstain (n : Nat) : BitCandidate n :=
  ⟨fun _ => .zero, fun _ => Or.inl rfl, zero_candidate_values⟩

def BitCandidate.selected (chosen : Fin (n + 1)) : BitCandidate n where
  bit j := if j = chosen then .one else .zero
  isBit j := by split <;> simp
  valid := Or.inr (vote_sum_one chosen).sound

/-- The old selected-index value is an exact specialization, not an E-only approximation. -/
theorem BitCandidate.selected_values (chosen : Fin (n + 1)) :
    (BitCandidate.selected chosen).values = vote chosen := rfl

end ExplainableCrypto.Helios.Symbolic
