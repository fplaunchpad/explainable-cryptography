import ExplainableCrypto.Helios.Symbolic.GeneralCandidateProtection
import ExplainableCrypto.Helios.Symbolic.BallotValueSPOT

namespace ExplainableCrypto.Helios.Symbolic.GeneralCandidateSPOT
open Historical

abbrev names : Names 1 := HistoricalFrameSPOT.names
abbrev abstain : CandidateSubstitution 1 Empty := (BitCandidate.abstain 1).substitution
abbrev selected : CandidateSubstitution 1 Empty := (BitCandidate.selected (1 : Fin 2)).substitution
abbrev hiddenZero : Ground := .unary .fst (.binary .pair (.const .zero) (.name 20))

def representedValue (j : Fin 2) : Ground :=
  if j = 0 then hiddenZero else .binary .add (.const .zero) (.const .one)

private theorem represented_correct (j : Fin 2) : EqE (representedValue j) (selected.value j) := by
  fin_cases j
  · exact (RootStep.fst (.const .zero) (.name 20)).sound
  · exact .equation .zero_one

def represented : CandidateSubstitution 1 Empty :=
  ⟨representedValue, selected.valid.congr (fun j => (represented_correct j).symm)⟩

/-- The components may be projection and E0-addition representatives, not literal bits. -/
theorem nonliteral_candidate_accepted :
    represented.value 0 ≠ .const .zero ∧ represented.value 0 ≠ .const .one ∧
    Accepted 1 (publicKey names) [] (General.ballot names 0 represented.value) :=
  ⟨by decide, by decide, General.honest_empty_board_accepts names 0 represented⟩

theorem represented_candidate_has_expected_bits :
    ∃ b : BitCandidate 1, (∀ j, EqE (represented.value j) (b.values j)) ∧
      b.bit 0 = .zero ∧ b.bit 1 = .one := by
  obtain ⟨b, hb⟩ := represented.bit_representative
  have hzero : EqE (Term.const (b.bit 0) : Ground) (.const .zero) := (hb 0).symm.trans (represented_correct 0)
  have hone : EqE (Term.const (b.bit 1) : Ground) (.const .one) := (hb 1).symm.trans (represented_correct 1)
  refine ⟨b, hb, ?_, ?_⟩
  · rcases b.isBit 0 with hz | ho
    · exact hz
    · rw [ho] at hzero
      exact False.elim (zero_not_one hzero.symm)
  · rcases b.isBit 1 with hz | ho
    · rw [hz] at hone
      exact False.elim (zero_not_one hone)
    · exact ho

/-- Numeric inversion sees through arbitrary reducible operands. -/
theorem delayed_numeric_inversion :
    EqE (.binary .add hiddenZero (.binary .add (.const .zero) (.const .one))) (.const .one) ∧
    EqE hiddenZero (.const .zero) ∧ EqE (Term.binary .add (.const .zero) (.const .one) : Ground) (.const .one) := by
  have hz := (RootStep.fst (Term.const .zero : Ground) (.name 20)).sound
  have ho : EqE (Term.binary .add (.const .zero) (.const .one) : Ground) (.const .one) := .equation .zero_one
  have he := (EqE.add_one_iff hiddenZero _).mpr (Or.inl ⟨hz, ho⟩)
  rcases (EqE.add_one_iff hiddenZero _).mp he with h | h
  · exact ⟨he, h.1, h.2⟩
  · exact False.elim (zero_not_one (hz.symm.trans h.1))

private theorem ok_not_bit : ¬ BitValue (Term.const .ok : Ground) := by
  rintro (hz | ho)
  · have hb := (irreducible_eqE_iff_base (constant_irreducible .ok) (constant_irreducible .zero)).mp hz
    cases hb.head_eq
  · have hb := (irreducible_eqE_iff_base (constant_irreducible .ok) (constant_irreducible .one)).mp ho
    cases hb.head_eq

/-- Kernel control for the gate's n=0 failure: the separating algebra is not complete. -/
theorem numeric_interpretation_not_candidate :
    (Term.const .ok : Ground).denote (fun _ => 0) (fun _ => 0) = 0 ∧
    ¬ CandidateValues (V := Empty) (n := 0) (fun _ => .const .ok) := ⟨rfl, ok_not_bit⟩

theorem honest_abstention_both_orders :
    Accepted 1 (publicKey names) [General.ballot names 0 abstain.value] (General.ballot names 1 selected.value) ∧
    Accepted 1 (publicKey names) [General.ballot names 0 selected.value] (General.ballot names 1 abstain.value) :=
  ⟨General.honest_accepts_after_other names HistoricalFrameSPOT.fixture_names_fresh 0 1 (by decide) abstain selected,
    General.honest_accepts_after_other names HistoricalFrameSPOT.fixture_names_fresh 0 1 (by decide) selected abstain⟩

theorem honest_double_abstention_accepts :
    Accepted 1 (publicKey names) [General.ballot names 0 abstain.value] (General.ballot names 1 abstain.value) :=
  General.honest_accepts_after_other names HistoricalFrameSPOT.fixture_names_fresh 0 1 (by decide) abstain abstain

/-- The previously omitted accepted all-zero value now has an honest constructor. -/
theorem honest_abstention_scope_filled :
    let ns : Names 0 := ⟨10, 11, fun i _ => 40 + i.val⟩
    General.ballot ns 0 (BitCandidate.abstain 0).values = BallotValueSPOT.abstention ∧
      Accepted 0 (publicKey ns) [] (General.ballot ns 0 (BitCandidate.abstain 0).values) := by
  dsimp only
  exact ⟨rfl, General.honest_empty_board_accepts _ _ (BitCandidate.abstain 0).substitution⟩

/-- All recipe values survive a change of vote representatives in either world. -/
theorem representative_recipe_values (swap : Bool) (r : Recipe 3) :
    EqE ((General.frame names swap represented abstain).eval r)
      ((General.frame names swap selected abstain).eval r) :=
  r.subst_congr _ _ (General.frame_congr names swap represented abstain selected abstain represented_correct (fun _ => .refl _))

/-- Valid representatives can fail the raw syntactic invariant while still having
an E-equal protected value. This is not an operational name leak. -/
theorem raw_protection_not_required :
    ((General.frame names false represented abstain).value 1).nonceSafe names.nonceNames = false ∧
    ∃ t : Ground, EqE ((General.frame names false represented abstain).value 1) t ∧
      t.nonceSafe names.nonceNames = true := by
  refine ⟨by decide, ?_⟩
  exact General.frame_recipe_protected_value names false represented abstain (.var 1) trivial

theorem represented_frame_nonce_not_deducible (r : Recipe 3) (hr : r.Public names.nonceNames) :
    ¬ EqE ((General.frame names false represented abstain).eval r) (.name 20) :=
  General.frame_nonce_not_deducible names false represented abstain r hr (by decide)

theorem represented_frame_composed_nonce_not_deducible (r : Recipe 3) (hr : r.Public names.nonceNames) (rest : Ground) :
    ¬ EqE ((General.frame names false represented abstain).eval r) (.binary .compose (.name 20) rest) :=
  General.frame_nonce_factor_not_deducible names false represented abstain r hr (name := 20) (by decide) _
    (by simp [Term.composeFactors])

/-- Ciphertext observation remains available even though its nonce cannot be deduced. -/
theorem represented_frame_public_ciphertext :
    EqE ((General.frame names false represented abstain).eval ((Term.var 1).project 0))
      (.ternary .penc (publicKey names) (.name 20) (.const .zero)) := by
  have hp := General.ballot_project_ciphertext names 0 represented.value 0
  have hmsg := represented_correct 0
  exact hp.trans (.ternary .penc (.refl _) (.refl _) hmsg)

theorem two_ones_not_candidate : ¬ CandidateValues (V := Empty) (n := 1) (fun _ => .const .one) := by
  rintro (hz | ho)
  · have h := (EqE.add_zero_iff (Term.const .one : Ground) (.const .one)).mp hz
    exact zero_not_one h.1.symm
  · exact two_not_one ho

/-- Dropping the source candidate condition invalidates the honest-validity claim. -/
theorem candidate_condition_required :
    ¬ ProofValid 1 (publicKey names) (General.ballot names 0 (fun _ => .const .one)) := by
  intro h
  exact two_ones_not_candidate (h.candidate_of_ciphertexts (fun j => .name (names.nonce 0 j))
    (fun _ => .const .one) (General.ballot_project_ciphertext names 0 (fun _ => .const .one)))

end ExplainableCrypto.Helios.Symbolic.GeneralCandidateSPOT
