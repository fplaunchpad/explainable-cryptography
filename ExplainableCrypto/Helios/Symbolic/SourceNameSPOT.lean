import ExplainableCrypto.Helios.Symbolic.SourceNameLabels
import ExplainableCrypto.Helios.Symbolic.SourceAtomicOutputSPOT
import ExplainableCrypto.Helios.Symbolic.SourceParallelSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceNameSPOT
open Historical General Source Extended

abbrev baseSwap : Nat ≃ Nat := Equiv.swap 0 40
abbrev channelSwap : Nat ≃ Nat := Equiv.swap 0 7

/-- Equal numeral indices across the three sorts are deliberately distinct. -/
theorem three_sorts_separate :
    (Agent.output 0 (.binary .pair (.name 0) (.var (0 : Nat)))
      (.input 0 (.output 0 (.var none) .nil))).mapNames baseSwap channelSwap =
    .output 7 (.binary .pair (.name 40) (.var 0))
      (.input 7 (.output 7 (.var none) .nil)) := by
  simp [Agent.mapNames,Term.mapNames,baseSwap,channelSwap]

/-- All proof fields, including the complete fourth ciphertext, move. -/
theorem full_proof_fields_move :
    (Term.spk (.binary .pair (.name 0) (.name 41)) (.name 0) (.const .one)
      (.ternary .penc (.binary .pair (.name 0) (.name 41)) (.name 0) (.const .one)) : Ground).mapNames baseSwap =
    .spk (.binary .pair (.name 40) (.name 41)) (.name 40) (.const .one)
      (.ternary .penc (.binary .pair (.name 40) (.name 41)) (.name 40) (.const .one)) := by
  simp [Term.mapNames,baseSwap,Equiv.swap_apply_def]

theorem structured_key_homomorphism_moves :
    EqE (Term.binary .mul
      (.ternary .penc (.binary .pair (.name 40) (.name 41)) (.name 40) (.const .zero))
      (.ternary .penc (.binary .pair (.name 40) (.name 41)) (.name 42) (.const .one)) : Ground)
      (.ternary .penc (.binary .pair (.name 40) (.name 41))
        (.binary .compose (.name 40) (.name 42)) (.binary .add (.const .zero) (.const .one))) := by
  have h : EqE (Term.binary .mul
      (.ternary .penc (.binary .pair (.name 0) (.name 41)) (.name 0) (.const .zero))
      (.ternary .penc (.binary .pair (.name 0) (.name 41)) (.name 42) (.const .one)) : Ground)
      (.ternary .penc (.binary .pair (.name 0) (.name 41))
        (.binary .compose (.name 0) (.name 42)) (.binary .add (.const .zero) (.const .one))) :=
    .equation (.homomorphic _ _ _ _ _)
  simpa [Term.mapNames,baseSwap,Equiv.swap_apply_def] using h.mapNames baseSwap

theorem full_ciphertext_partial_decryption_moves :
    EqE (Term.binary .dec
      (.binary .partialDecrypt (.binary .pair (.name 40) (.name 41))
        (.ternary .penc (.unary .pk (.binary .pair (.name 40) (.name 41))) (.name 40) (.name 42)))
      (.ternary .penc (.unary .pk (.binary .pair (.name 40) (.name 41))) (.name 40) (.name 42)) : Ground) (.name 42) := by
  have h : EqE (Term.binary .dec
      (.binary .partialDecrypt (.binary .pair (.name 0) (.name 41))
        (.ternary .penc (.unary .pk (.binary .pair (.name 0) (.name 41))) (.name 0) (.name 42)))
      (.ternary .penc (.unary .pk (.binary .pair (.name 0) (.name 41))) (.name 0) (.name 42)) : Ground) (.name 42) :=
    .equation (.partial_decrypt _ _ _)
  simpa [Term.mapNames,baseSwap,Equiv.swap_apply_def] using h.mapNames baseSwap

theorem changed_policy_required :
    ¬ (Term.name 0 : Ground).Public {0} ∧
    ¬ ((Term.name 0 : Ground).mapNames baseSwap).Public (({0} : Finset Nat).image baseSwap) ∧
    ((Term.name 0 : Ground).mapNames baseSwap).Public {0} := by
  simp [Term.Public,Term.mapNames,baseSwap]

/-- A noninjective map really creates a new full-E equality. -/
theorem merging_names_changes_equality :
    ¬ EqE (.name 0 : Ground) (.name 1) ∧
    EqE ((.name 0 : Ground).mapNames (fun _ => 40)) ((.name 1 : Ground).mapNames (fun _ => 40)) := by
  refine ⟨?_,.refl _⟩
  intro h
  have hn := (EqE.name_iff 0 1).mp h
  omega

theorem merging_names_changes_negative_guard :
    (Formula.unequal (.name 0) (.name 1) : Formula Empty).Holds Empty.elim ∧
    ¬ ((Formula.unequal (.name 0) (.name 1) : Formula Empty).mapNames (fun _ => 40)).Holds Empty.elim := by
  change (¬ EqE (.name 0 : Ground) (.name 1)) ∧ ¬ (¬ EqE (.name 40 : Ground) (.name 40))
  exact ⟨merging_names_changes_equality.1,fun h => h (.refl _)⟩

theorem permutation_preserves_negative_guard :
    ((Formula.unequal (.name 0) (.name 1) : Formula Empty).mapNames baseSwap).Holds Empty.elim :=
  (Formula.holds_mapNames_ground _ baseSwap).mpr merging_names_changes_negative_guard.1

/-- Renaming just one endpoint leaves no communication partner. -/
theorem one_endpoint_rename_blocks (q : Agent Empty) :
    ¬ Agent.Tau (.par (.output 7 (.name 40) .nil) (.input 0 (.output 7 (.var none) .nil))) q := by
  intro h
  rcases h.enabled with ⟨f,a,b,hm⟩ | ⟨c,m,a,b,ho,hi⟩
  · simp [Agent.threads,Agent.threadList] at hm
  · simp [Agent.threads,Agent.threadList] at ho hi
    omega

theorem omitted_payload_rename_differs :
    (Agent.output 0 (.name 0) .nil : Agent Empty).mapNames baseSwap channelSwap ≠
      .output 7 (.name 0) .nil := by
  simp [Agent.mapNames,Term.mapNames,baseSwap,channelSwap]

/-- The general theorem also covers the actual whole election handshake. -/
theorem whole_election_handshake_moves (swap : Bool) (extra : Nat) :
    Agent.Tau
      ((electionBody SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right extra Channels.canonical).mapNames baseSwap channelSwap)
      ((residual SharedTallySPOT.names swap SharedTallySPOT.left SharedTallySPOT.right extra Channels.canonical .firstReceived).mapNames baseSwap channelSwap) :=
  (residual_receiveFirst _ _ _ _ _ _).mapNames baseSwap channelSwap

/-- Literal names move through variable Scope without moving either binder. -/
theorem scoped_output_binders_stay :
    BoundOutput
      (.newVar (.par (.active none (.name 0)) (.plain (.output 7 (.name 41) .nil))) : Extended (Fin 1)) 7
      (.newVar (.par (.active none (.name 0)) (.par (.active (some none) (.name 41)) (.plain .nil)))) := by
  simpa [Extended.mapNames,Agent.mapNames,Term.mapNames,baseSwap,channelSwap,Equiv.swap_apply_def] using
    SourceAtomicOutputSPOT.output_crosses_variable_scope.mapNames baseSwap channelSwap
end ExplainableCrypto.Helios.Symbolic.SourceNameSPOT
