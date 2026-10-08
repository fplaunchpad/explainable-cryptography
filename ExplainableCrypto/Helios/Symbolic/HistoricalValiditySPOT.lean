import ExplainableCrypto.Helios.Symbolic.HistoricalValidity
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT

namespace ExplainableCrypto.Helios.Symbolic.HistoricalValiditySPOT
open Historical

theorem both_two_candidate_positions_accept :
    Accepted 1 (publicKey HistoricalFrameSPOT.names) [] (ballot HistoricalFrameSPOT.names 0 0) ∧
    Accepted 1 (publicKey HistoricalFrameSPOT.names) [] (ballot HistoricalFrameSPOT.names 0 1) :=
  ⟨honest_empty_board_accepts _ _ _, honest_empty_board_accepts _ _ _⟩

theorem fresh_second_ballot_accepts (swap : Bool) :
    Accepted 1 (publicKey HistoricalFrameSPOT.names)
      [ballot HistoricalFrameSPOT.names 0 (choice swap 0 1 0)]
      (ballot HistoricalFrameSPOT.names 1 (choice swap 0 1 1)) :=
  honest_accepts_after_other _ HistoricalFrameSPOT.fixture_names_fresh 0 1 (by decide) _ _

theorem replay_rejected (chosen : Fin 2) :
    ¬ Accepted 1 (publicKey HistoricalFrameSPOT.names)
      [ballot HistoricalFrameSPOT.names 0 chosen] (ballot HistoricalFrameSPOT.names 0 chosen) :=
  accepted_excludes_replay _ _ _ _ (by simp)

def colliding : Names 1 := ⟨10, 11, fun _ j => 20 + j.val⟩

theorem nonce_collision_rejected :
    ¬ Accepted 1 (publicKey colliding) [ballot colliding 0 0] (ballot colliding 1 0) :=
  accepted_excludes_replay _ _ _ _ (by decide)

theorem two_ones_do_not_normalize_to_one :
    ¬ EqE (Term.binary .add (.const .one) (.const .one) : Ground) (.const .one) := by
  intro h
  have hi : Irreducible (Term.binary .add (.const .one) (.const .one) : Ground) :=
    irreducible_of_add_atoms_empty _ (by simp [Term.addSummary, AddSummary.combine, AddSummary.number])
  have he := (irreducible_eqE_iff_base hi (constant_irreducible .one)).mp h
  exact AddSummary.two_ones_not_one he.add_summary

theorem first_position_sum : BaseEq (foldCandidates .add (vote (0 : Fin 3))) (.const .one) := vote_sum_one _
theorem last_position_sum : BaseEq (foldCandidates .add (vote (2 : Fin 3))) (.const .one) := vote_sum_one _

theorem aggregate_has_expected_plaintext :
    EqE (foldCandidates .mul (ciphertext HistoricalFrameSPOT.names 0 1))
      (.ternary .penc (.unary .pk (.name 10)) (.binary .compose (.name 20) (.name 21)) (.const .one)) :=
  ciphertext_product _ _ _

end ExplainableCrypto.Helios.Symbolic.HistoricalValiditySPOT
