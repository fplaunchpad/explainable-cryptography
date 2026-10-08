import ExplainableCrypto.Helios.Symbolic.PartialKeyObservationInduction
import ExplainableCrypto.Helios.Symbolic.StuckDestructorSPOT

namespace ExplainableCrypto.Helios.Symbolic.DecryptionProbeSPOT
open Historical General
abbrev names := ProofObservationSPOT.names
abbrev left := ProofObservationSPOT.left
abbrev right := ProofObservationSPOT.right
abbrev reveal := StuckDestructorSPOT.reveal
abbrev cipher (nonce : Nat) : Ground := keyCiphertext (.name 40) (.name nonce) (.name 90)
abbrev structuredKey : Ground := .binary .partialDecrypt (.name 40) (.name 50)
abbrev structuredCipher : Ground := keyCiphertext structuredKey (.name 60) (.name 90)

/-- The input-0 E5-omission witness: a structured secret key really decrypts,
although neither the ordinary inner key nor the E6 binding matches. -/
theorem direct_structured_key_required :
    (∃ m, DecryptionMatch structuredKey structuredCipher m) ∧
    EqE (.binary .dec structuredKey structuredCipher) (.name 90) ∧
    ¬ EqE (.unary .pk structuredKey) (.unary .pk (.name 40)) := by
  refine ⟨⟨.name 90, structuredKey, .name 60, Or.inl (.refl _), .refl _⟩,
    (RootStep.decrypt _ _ _).sound, ?_⟩
  intro he
  obtain ⟨_, _, h, _⟩ := ((EqE.pk_iff _ _).mp he).passive_binary_irreducible_shape
    (Or.inr rfl) (name_irreducible 40)
  cases h

/-- The input-0 binding-omission witness: the inner key agrees, but a changed
nonce makes the complete ciphertext different and prevents E6. -/
theorem complete_binding_required :
    EqE (.unary .pk (.name 40) : Ground) (.unary .pk (.name 40)) ∧
    ¬ (∃ m, DecryptionMatch (.binary .partialDecrypt (.name 40) (cipher 51)) (cipher 50) m) := by
  refine ⟨.refl _, ?_⟩
  intro hm
  rcases (DecryptionMatch.partial_key_iff _ _ _ _ _ _ (EqE.refl (cipher 50))).mp hm with h | ⟨_, h⟩
  · obtain ⟨_, _, hshape, _⟩ := ((EqE.pk_iff _ _).mp h).symm.passive_binary_irreducible_shape
      (Or.inr rfl) (name_irreducible 40)
    cases hshape
  · have hn := (EqE.name_iff 51 50).mp ((EqE.penc_iff _ _ _ _ _ _).mp h).2.1
    omega

/-- Reducible key and complete binding values produce an actual reachable
match, with the independently specified name-90 plaintext. -/
theorem delayed_matching_values :
    (∃ m, DecryptionMatch (reveal (.binary .partialDecrypt (reveal (.name 40)) (reveal (cipher 50))))
      (reveal (cipher 50)) m) ∧
    EqE (.binary .dec (reveal (.binary .partialDecrypt (reveal (.name 40)) (reveal (cipher 50))))
      (reveal (cipher 50))) (.name 90) := by
  have hk : EqE (reveal (.name 40)) (.name 40) := (RootStep.fst _ _).sound
  have hb : EqE (reveal (cipher 50)) (cipher 50) := (RootStep.fst _ _).sound
  have ha : EqE (reveal (.binary .partialDecrypt (reveal (.name 40)) (reveal (cipher 50))))
      (.binary .partialDecrypt (.name 40) (reveal (cipher 50))) :=
    (RootStep.fst _ _).sound.trans (.binary .partialDecrypt hk (.refl _))
  exact ⟨DecryptionMatch.exists_of_values hb (Or.inr ha),
    (EqE.binary .dec (ha.trans (.binary .partialDecrypt (.refl _) hb)) hb).trans
      (RootStep.partial_decrypt _ _ _).sound⟩

abbrev probeFrame (good : Bool) : Frame ∅ 3 := ⟨fun v =>
  if v = 0 then .name 40 else if v = 1 then cipher (if good then 50 else 51) else cipher 50⟩

/-- A changed published binding enables E6. The public binding/ciphertext
comparison actually detects it below the decryption comparison budget. -/
theorem binding_probe_detects_new_match :
    ¬ (∃ m, DecryptionMatch ((probeFrame false).eval (.binary .partialDecrypt (.var 0) (.var 1)))
      ((probeFrame false).eval (.var 2)) m) ∧
    (∃ m, DecryptionMatch ((probeFrame true).eval (.binary .partialDecrypt (.var 0) (.var 1)))
      ((probeFrame true).eval (.var 2)) m) ∧
    ¬ (probeFrame false).ObservationsBelow (probeFrame true) 6 := by
  refine ⟨complete_binding_required.2,
    ⟨.name 90, .name 40, .name 50, Or.inr (.refl _), .refl _⟩, ?_⟩
  intro hobs
  have he := (hobs (.var 1) (.var 2) trivial trivial (by decide)).mpr (EqE.refl (cipher 50))
  have hn := (EqE.name_iff 51 50).mp ((EqE.penc_iff _ _ _ _ _ _).mp he).2.1
  omega

abbrev first : Recipe 3 := .unary .fst (.var 1)
abbrev decrypt (name : Nat) : Recipe 3 := .binary .dec (.binary .partialDecrypt (.name 40) (.name name)) first

private theorem first_value (swap : Bool) (a b : CandidateSubstitution 1 Empty) :
    EqE ((General.frame names swap a b).eval first)
      (General.ciphertext names 0 (General.choice swap a b 0).value 0) := by
  simpa [Frame.eval, first, Term.project, Term.drop, Term.subst, General.frame] using
    General.ballot_project_ciphertext names 0 (General.choice swap a b 0).value 0

private theorem first_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty) :
    MinimalRecipe names.restricted (General.frame names swap a b).value first := by
  refine ⟨trivial, ?_⟩
  intro r _ he
  exact ciphertext_recipe_size_ge_two (General.frame names swap a b).value _ _ _
    (fun v => General.frame_handle_not_ciphertext names swap a b v _ _ _) (he.symm.trans (first_value swap a b))

private theorem wrong_partial_no_match (swap : Bool) (a b : CandidateSubstitution 1 Empty) (name : Nat) :
    ∀ m, ¬ DecryptionMatch (.binary .partialDecrypt (.name 40) (.name name))
      ((General.frame names swap a b).eval first) m := by
  intro m hm
  rcases (DecryptionMatch.partial_key_iff _ _ _ _ _ _ (first_value swap a b)).mp ⟨m, hm⟩ with h | ⟨h, _⟩
  · have he : EqE (.name 10 : Ground) (.binary .partialDecrypt (.name 40) (.name name)) := (EqE.pk_iff _ _).mp h
    obtain ⟨_, _, hs, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (name_irreducible 10)
    cases hs
  · have he : 10 = 40 := (EqE.name_iff _ _).mp ((EqE.pk_iff _ _).mp h)
    omega

/-- A partial key of public names applied to the first honest ciphertext is an
exact six-node minimum for every valid candidate assignment in this fixture. -/
theorem six_node_minimum (swap : Bool) (a b : CandidateSubstitution 1 Empty)
    (name : Nat) (hn : name ∉ names.restricted) :
    MinimalRecipe names.restricted (General.frame names swap a b).value (decrypt name) ∧
    (decrypt name).nodeCount = 6 := by
  have hp : (decrypt name).Public names.restricted := ⟨⟨by change 40 ∉ names.restricted; decide, hn⟩, trivial⟩
  obtain ⟨r, hr, he⟩ := exists_minimal_recipe (σ := (General.frame names swap a b).value) _ hp
  have hno := wrong_partial_no_match swap a b name
  obtain ⟨u, v, rfl, huv⟩ := minimum_stuck_decryption_form names swap a b names.restricted r hr hno he.symm
  have hargs := (EqE.decryption_iff_of_no_match _ _ _ _ hno huv).mp he
  have hpmin := PartialDecryptionObservationSPOT.literal_partial_minimum swap a b 40 name (by decide) hn
  have hleft := hpmin.least u hr.isPublic.1 hargs.1
  have hright := (first_minimum swap a b).least v hr.isPublic.2 hargs.2
  refine ⟨⟨hp, fun s hs hes => ?_⟩, rfl⟩
  have hle := hr.least s hs (he.symm.trans hes)
  change 3 ≤ u.nodeCount at hleft
  change 2 ≤ v.nodeCount at hright
  simp only [Term.nodeCount] at hle ⊢
  omega

/-- The full two-sided branch is instantiated by distinct six-node minima.
The bounded premise comes from diagonal candidates, not an assumed privacy
result. The negative observation rules out constant stuck outputs. -/
theorem unequal_minimum_branch :
    ¬ EqE ((General.frame names false left left).eval (decrypt 50))
      ((General.frame names false left left).eval (decrypt 51)) ∧
    (EqE ((General.frame names false left left).eval (decrypt 50))
        ((General.frame names false left left).eval (decrypt 51)) ↔
      EqE ((General.frame names true left left).eval (decrypt 50))
        ((General.frame names true left left).eval (decrypt 51))) := by
  have hr := (six_node_minimum false left left 50 (by decide)).1
  have hs := (six_node_minimum false left left 51 (by decide)).1
  refine ⟨?_, minimum_partial_key_decryption_equality_swap names left left _ _ _ _ hr hs
    (.refl _) (first_value false left left) (.refl _) (first_value false left left)
    (CiphertextObservationSPOT.diagonal_observations _)⟩
  intro he
  have ha := ((EqE.decryption_iff_of_no_match _ _ _ _ (wrong_partial_no_match false left left 50)
    (wrong_partial_no_match false left left 51)).mp he).1
  have hn := (EqE.name_iff 50 51).mp ((EqE.partialDecrypt_iff _ _ _ _).mp ha).2
  omega

/-- The failure theorem accepts a reducible supplied partial-key target and
actual six-node minimum syntax. No destination minimum-size premise is supplied. -/
theorem failure_transfer_with_reducible_target :
    ∀ m, ¬ DecryptionMatch ((General.frame names true left left).eval (.binary .partialDecrypt (.name 40) (.name 50)))
      ((General.frame names true left left).eval first) m := by
  have ha : EqE ((General.frame names false left left).eval (.binary .partialDecrypt (.name 40) (.name 50)))
      (.binary .partialDecrypt (reveal (.name 40)) (.name 50)) :=
    .binary .partialDecrypt (RootStep.fst _ _).sound.symm (.refl _)
  exact minimum_partial_key_decryption_failure names left left _ _
    (six_node_minimum false left left 50 (by decide)).1 ha (first_value false left left)
    (CiphertextObservationSPOT.diagonal_observations _)

/-- A coherent fully public ciphertext assembly has a real E5 match with its
structured key in both worlds. The match-transfer theorem does not reject all
partial-key decryptions or assume minimum size for this positive control. -/
theorem assembly_match_transfer_positive :
    ∃ m, DecryptionMatch ((General.frame names true left left).eval (.binary .partialDecrypt (.name 40) (.name 50)))
      ((General.frame names true left left).eval
        (.ternary .penc (.unary .pk (.binary .partialDecrypt (.name 40) (.name 50))) (.name 60) (.name 90))) m := by
  let t : CiphertextAssembly 1 := .constructed (.unary .pk (.binary .partialDecrypt (.name 40) (.name 50))) (.name 60) (.name 90)
  have hp : (Term.binary .dec (.binary .partialDecrypt (.name 40) (.name 50)) t.recipe).Public names.restricted := by
    change (40 ∉ names.restricted ∧ 50 ∉ names.restricted) ∧
      (40 ∉ names.restricted ∧ 50 ∉ names.restricted) ∧ 60 ∉ names.restricted ∧ 90 ∉ names.restricted
    decide
  exact (assembly_partial_key_match_swap names left left (.name 40) (.name 50) t hp trivial
    (CiphertextObservationSPOT.diagonal_observations _)).mp direct_structured_key_required.1

end ExplainableCrypto.Helios.Symbolic.DecryptionProbeSPOT
