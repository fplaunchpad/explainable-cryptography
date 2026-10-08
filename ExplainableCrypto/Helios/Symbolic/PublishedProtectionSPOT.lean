import ExplainableCrypto.Helios.Symbolic.PublishedProtection
import ExplainableCrypto.Helios.Symbolic.OpaqueProtectionExperiments
import ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT

namespace ExplainableCrypto.Helios.Symbolic.PublishedProtectionSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right

/-- Name secrecy covers all nested new-handle recipes even with arbitrary
submission syntax. No acceptance premise can make this control vacuous. -/
theorem partial_secret_not_deducible (swap : Bool) (rs : List (Recipe 3))
    (r : Recipe 4) (hr : r.Public names.restricted) :
    ¬ EqE ((partialFrame names swap left right rs).eval r) (.name names.secretKey) :=
  partial_frame_name_not_deducible names swap left right rs r hr (by decide)

/-- Final-frame protection does not rely on ballot acceptance: the public
malformed submission is permitted and all final public recipes remain covered. -/
theorem malformed_public_submission_keeps_secret (swap : Bool)
    (r : Recipe 5) (hr : r.Public names.restricted) :
    ¬ EqE ((finalFrame names swap left right [.const .bottom]).eval r) (.name names.secretKey) := by
  apply final_frame_name_not_deducible names swap left right [.const .bottom] _ r hr (by decide)
  intro s hs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
  subst s
  trivial

/-- The new invariant protects an actual published partial that the old
nonce invariant rejects, while the partial remains publicly available. -/
theorem published_partial_is_available (swap : Bool) :
    (tallyPartial names swap left right [] 0).nonceSafe names.restricted = false ∧
    (tallyPartial names swap left right [] 0).opaqueSafe names.restricted = true ∧
    EqE ((partialFrame names swap left right []).eval ((Term.var 3).project 0))
      (tallyPartial names swap left right [] 0) := by
  refine ⟨?_,rfl,partialFrame_partial_project names swap left right [] 0⟩
  simp [tallyPartial,Term.nonceSafe,Names.restricted]

/-- Nonliteral valid ballots may fail raw protection. Their actual frame
values nevertheless have protected E-representatives. -/
theorem raw_unsafe_valid_ballot_supported :
    ((frame names false left right).value 1).opaqueSafe names.restricted = false ∧
    OpaqueProtectedValue names.restricted ((frame names false left right).value 1) :=
  ⟨by decide,initial_frame_opaque_protected names false left right 1⟩

/-- Exposing fields as a pair really leaks the secret; treating pair as an
opaque partial would make the invariant unsound. -/
theorem pair_publication_leaks :
    let φ : Frame names.restricted 1 := ⟨fun _ => .binary .pair (.name names.secretKey) (.const .one)⟩
    let r : Recipe 1 := .unary .fst (.var 0)
    r.Public names.restricted ∧ EqE (φ.eval r) (.name names.secretKey) ∧
      ¬ φ.OpaqueProtected := by
  refine ⟨trivial,(RootStep.fst _ _).sound,?_⟩
  intro h
  exact h.name_not_deducible (.unary .fst (.var 0)) trivial (by decide) (RootStep.fst _ _).sound

/-- E6 can expose its supplied ciphertext plaintext. The protection check
must reject this input even though the partial itself is opaque. -/
theorem plaintext_protection_required :
    let c : Ground := keyCiphertext (.name 40) (.name 50) (.name names.secretKey)
    let t := Term.binary .dec (.binary .partialDecrypt (.name 40) c) c
    t.opaqueSafe names.restricted = false ∧ EqE t (.name names.secretKey) :=
  ⟨by decide,(RootStep.partial_decrypt _ _ _).sound⟩

/-- Raw protection is directional under E. The value property handles
expansions that introduce irrelevant occurrences under a discarded field. -/
theorem raw_full_E_invariance_refuted :
    let t : Ground := .unary .fst (.binary .pair (.const .one) (.name names.secretKey))
    t.opaqueSafe names.restricted = false ∧ EqE t (.const .one) ∧
      OpaqueProtectedValue names.restricted t :=
  ⟨by decide,(RootStep.fst _ _).sound,
    (OpaqueProtectedValue.of_safe (rfl : (Term.const .one : Ground).opaqueSafe names.restricted = true)).of_eq
      (RootStep.fst _ _).sound.symm⟩

/-- Nested new-handle computations cannot recover a nonce with an arbitrary
reducible composition remainder. This reuses persistent name-factor analysis. -/
theorem composed_nonce_not_deducible (swap : Bool) (r : Recipe 4)
    (hr : r.Public names.restricted) (rest : Ground) :
    ¬ EqE ((partialFrame names swap left right []).eval r)
      (.binary .compose (.name (names.nonce 0 0)) rest) := by
  apply (partial_frame_opaque_protected names swap left right []).name_factor_not_deducible r hr (name := names.nonce 0 0) (by decide)
  simp [Term.composeFactors]

/-- Decryption still works under the stronger name invariant, via both rules.
The E5 output is a distinct public name and the E6 candidate result is one. -/
theorem both_decryption_rules_remain_usable (swap : Bool) :
    (partialFrame names swap left right []).OpaqueProtected ∧
    EqE (.binary .dec (tallyPartial names swap left right [] 0)
      (keyCiphertext (tallyPartial names swap left right [] 0) (.name 60) (.name 90))) (.name 90) ∧
    EqE (tallyResult names swap left right [] 1) (.const .one) :=
  ⟨partial_frame_opaque_protected names swap left right [],
    (TrusteePartialSPOT.new_cipher_uses_partial_as_secret swap (.name 60) (.name 90)).2,
    SharedTallySPOT.nonliteral_two_candidate_tally.2 swap⟩

/-- Constructed public keys remain distinct from the election key after
publication, including keys whose secret recipe uses a partial projection. -/
theorem constructed_partial_key_is_not_election_key (swap : Bool) :
    ¬ EqE ((partialFrame names swap left right []).eval (.unary .pk ((Term.var 3).project 0)))
      (publicKey names) :=
  partial_frame_constructed_key_not_election_key names swap left right [] _
    ((show (Term.var 3 : Recipe 4).Public names.restricted from trivial).project 0)

/-- A nested partial constructor using a published partial as its first
argument cannot become another trustee partial. The source slot is available. -/
theorem nested_partial_cannot_forge_trustee_partial (swap : Bool) :
    ¬ EqE ((partialFrame names swap left right []).eval
      (.binary .partialDecrypt ((Term.var 3).project 0) (Recipe.lift (tallyRecipe [] (1 : Fin 2)))))
      (tallyPartial names swap left right [] 1) :=
  partial_frame_constructed_partial_not_trustee_partial names swap left right [] _ _
    ((show (Term.var 3 : Recipe 4).Public names.restricted from trivial).project 0) _

end ExplainableCrypto.Helios.Symbolic.PublishedProtectionSPOT
