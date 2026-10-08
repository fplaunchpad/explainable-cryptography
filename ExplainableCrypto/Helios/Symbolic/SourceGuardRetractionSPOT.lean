import ExplainableCrypto.Helios.Symbolic.SourceElectionGuardRetractions
import ExplainableCrypto.Helios.Symbolic.SourceConditionalLocationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceGuardRetractionSPOT
open Historical General Source

def collapse (n : Nat) : Nat := if n=50 then 40 else n
def recover (n : Nat) : Nat := if n=40 then 50 else n
abbrev dead : Ground := .unary .fst (.binary .pair (.name 50) (.name 40))
abbrev goodGuard : Formula Empty := .both (.equal dead (.name 50)) (.unequal dead (.name 41))
abbrev badGuard : Formula Empty := .equal dead (.name 41)
abbrev futureGuard : Formula Empty := .unequal (.name 50) (.name 40)
abbrev fullPayload : Ground := .spk (.const .ok) (.const .one) (.const .zero) (.name 40)
abbrev continuation : Agent Empty := .output 7 fullPayload (.branch futureGuard .nil .nil)

theorem map_is_not_injective : collapse 50 = collapse 40 ∧ (50 : Nat) ≠ 40 := by decide

theorem main_name_recovers : (Term.name 50 : Ground).NameRetracts collapse recover := by
  change EqE (.name 50) (.name 50)
  exact .refl _

theorem other_name_recovers : (Term.name 41 : Ground).NameRetracts collapse recover := by
  change EqE (.name 41) (.name 41)
  exact .refl _

theorem dead_field_recovers_modulo_E : dead.NameRetracts collapse recover :=
  main_name_recovers.congr (EqE.equation (.fst _ _)).symm

theorem dead_field_does_not_recover_literally : (dead.mapNames collapse).mapNames recover ≠ dead := by decide

theorem dead_field_faithfulness_still_fails :
    ¬ NameAssignment.FaithfulOn (fun n => match n with | .base n => collapse n | .channel c => c)
      SourceNamedVisibleSPOT.expandedBinding.nameSupport := by
  intro h
  have he := h (a := .base 50) (b := .base 40) (by decide) (by decide) rfl
  cases he

theorem whole_guard_recovers : goodGuard.NameRetracts collapse recover :=
  Formula.EquivE.both (Formula.EquivE.equal dead_field_recovers_modulo_E main_name_recovers)
    (Formula.EquivE.unequal dead_field_recovers_modulo_E other_name_recovers)

theorem unequal_fields_remain_unequal : ¬ EqE dead (.name 41) := by
  intro h
  have he := (EqE.name_iff 50 41).mp ((EqE.equation (.fst _ _)).symm.trans h)
  cases he

theorem true_guard_and_its_image_hold :
    goodGuard.Holds Empty.elim ∧ (goodGuard.mapNames collapse).Holds Empty.elim := by
  have hh : goodGuard.Holds Empty.elim := ⟨EqE.equation (.fst _ _),unequal_fields_remain_unequal⟩
  exact ⟨hh,whole_guard_recovers.holds_mapNames.mpr hh⟩

theorem false_guard_and_its_image_fail :
    ¬ badGuard.Holds Empty.elim ∧ ¬ (badGuard.mapNames collapse).Holds Empty.elim := by
  have hr : badGuard.NameRetracts collapse recover :=
    Formula.EquivE.equal dead_field_recovers_modulo_E other_name_recovers
  exact ⟨unequal_fields_remain_unequal,fun h => unequal_fields_remain_unequal (hr.holds_mapNames.mp h)⟩

theorem successful_step_keeps_complete_continuation :
    Agent.Tau ((Agent.branch goodGuard continuation .nil).mapNames collapse id)
      (continuation.mapNames collapse id) :=
  (Agent.Tau.of_core (.thenBranch _ _ _ true_guard_and_its_image_hold.1)).mapNames_of_guard_retractions
    collapse recover id whole_guard_recovers

theorem failed_step_keeps_else_continuation :
    Agent.Tau ((Agent.branch badGuard .nil continuation).mapNames collapse id)
      (continuation.mapNames collapse id) :=
  (Agent.Tau.of_core (.elseBranch _ _ _ false_guard_and_its_image_fail.1)).mapNames_of_guard_retractions
    collapse recover id (Formula.EquivE.equal dead_field_recovers_modulo_E other_name_recovers)

theorem mapped_true_guard_cannot_take_null_else :
    ¬ Agent.CoreStep ((Agent.branch goodGuard continuation .nil).mapNames collapse id) .nil := by
  intro h
  cases h with
  | elseBranch φ a b hh => exact hh true_guard_and_its_image_hold.2

theorem mapped_payload_retains_fourth_field :
    continuation.mapNames collapse id =
      .output 7 (.spk (.const .ok) (.const .one) (.const .zero) (.name 40))
        (.branch (futureGuard.mapNames collapse) .nil .nil) := rfl

theorem essential_collision_has_no_inverse (g : Nat → Nat) :
    ¬ ((Term.name 50 : Ground).NameRetracts collapse g ∧
      (Term.name 40 : Ground).NameRetracts collapse g) := by
  rintro ⟨ha,hb⟩
  have he := (EqE.name_iff 50 40).mp
    ((EqE.mapNames_iff_of_retractions (.name 50) (.name 40) collapse g ha hb).mp (.refl _))
  cases he

theorem future_guard_does_not_retract : ¬ futureGuard.NameRetracts collapse recover := by
  intro h
  cases h with
  | unequal ha hb => exact essential_collision_has_no_inverse recover ⟨ha,hb⟩

theorem future_guard_is_not_a_current_premise :
    (Agent.branch goodGuard continuation .nil).ReadyGuardsRetract collapse recover ∧
      ¬ futureGuard.NameRetracts collapse recover :=
  ⟨whole_guard_recovers,future_guard_does_not_retract⟩

theorem full_proof_does_not_retract_with_bad_fourth_field :
    ¬ fullPayload.NameRetracts collapse recover := by
  intro h
  have hd := ((EqE.spk_iff _ _ _ _ _ _ _ _).mp h).2.2.2
  have he := (EqE.name_iff 50 40).mp hd
  cases he

theorem essential_ciphertext_field_does_not_retract :
    ¬ (Term.ternary .penc (.const .ok) (.const .zero) (.name 40) : Ground).NameRetracts collapse recover := by
  intro h
  have hd := ((EqE.penc_iff _ _ _ _ _ _).mp h).2.2
  have he := (EqE.name_iff 50 40).mp hd
  cases he

theorem actual_extended_conditional_transports :
    ∃ q : Agent Empty,
      Agent.Tau ((Agent.branch goodGuard continuation .nil).mapNames collapse id) (q.mapNames collapse id) ∧
      ((Extended.plain continuation).mapNames collapse id).Realizes
        (fun v : Empty => (Empty.elim v : Ground).mapNames collapse) (q.mapNames collapse id) :=
  (Extended.Reduction.thenBranch goodGuard continuation .nil true_guard_and_its_image_hold.1).realizes_mapNames_of_guard_retractions
    Empty.elim (.refl _) collapse recover id whole_guard_recovers

theorem literal_replay_check_transports (swap : Bool) (e k : Nat ≃ Nat) :
    Agent.Tau
      ((residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical
        (.check [] (.var 1))).mapNames e k)
      ((residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right 1 Channels.canonical
        (.rejected [])).mapNames e k) := by
  have h := (SourceInternalSPOT.accepted_and_rejected_checks_exist swap).2
  exact residual_check_tau_mapNames_of_retractions _ _ _ _ _ _ _ _ e e.symm k
    (Term.NameRetracts.of_inverse _ e) (Term.NameRetracts.of_inverse _ e)
    (fun t _ => Term.NameRetracts.of_inverse t e) h

end ExplainableCrypto.Helios.Symbolic.SourceGuardRetractionSPOT
