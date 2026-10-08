import ExplainableCrypto.Helios.Symbolic.ExpandedPartialTransport
import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments
import ExplainableCrypto.Helios.Symbolic.TrusteePartialSPOT

namespace ExplainableCrypto.Helios.Symbolic.ExpandedOriginSPOT
open Historical General
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private theorem numeric (swap : Bool) : ExpandedResultsNumeric names swap left right [] :=
  accepted_expanded_results_numeric names HistoricalFrameSPOT.fixture_names_fresh left right [] (by simp) trivial swap

/-- A ciphertext-valued atomic handle cannot have the required smaller
plaintext certificate. Dropping the generic handle premise is unsound. -/
theorem ciphertext_handle_premise_required :
    EqE (ExpandedOriginExperiments.cipherHandle.eval (.var 0))
      (keyCiphertext (.name 40) (.name 50) (.const .one)) ∧
    ¬ (∃ p s, CiphertextProduct ExpandedOriginExperiments.cipherHandle.value
      (.unary .pk (.name 40)) (.var 0) p s) := by
  refine ⟨.refl _,?_⟩
  rintro ⟨p,s,hp⟩
  have hs := hp.plaintext_smaller
  have hpos := p.nodeCount_pos
  change p.nodeCount < 1 at hs
  omega

/-- Ciphertexts with a public-name payload obtain an actual smaller public
plaintext recipe. The result does not restrict constructed payloads to bits. -/
theorem constructed_ciphertext_has_public_plaintext (swap : Bool) :
    let r : Recipe (ExpandedHandles 1) := .ternary .penc (.unary .pk (.var (expandedPartial 0))) (.name 60) (.name 90)
    ∃ m p, MinimalRecipe names.restricted (world swap).value m ∧ EqE ((world swap).eval r) ((world swap).eval m) ∧
      p.Public names.restricted ∧ p.nodeCount < m.nodeCount ∧ EqE ((world swap).eval p) (.name 90) := by
  let r : Recipe (ExpandedHandles 1) := .ternary .penc (.unary .pk (.var (expandedPartial 0))) (.name 60) (.name 90)
  have hr : r.Public names.restricted := by
    change True ∧ 60 ∉ names.restricted ∧ 90 ∉ names.restricted
    decide
  obtain ⟨m,hm,he⟩ := exists_minimal_recipe (σ := (world swap).value) r hr
  obtain ⟨p,s,_,hp,hsize,_,hvalue⟩ := expanded_minimum_ciphertext_certificate names swap left right [] (numeric swap)
    names.restricted m hm he.symm
  exact ⟨m,p,hm,he,hp,hsize,hvalue⟩

/-- Both origin alternatives are inhabited: a borrowed slot and a constructed
partial with minimum children. The constructed value cannot alias a trustee. -/
theorem constructed_and_borrowed_minima (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
    MinimalRecipe names.restricted (world swap).value a ∧
    MinimalRecipe names.restricted (world swap).value (.binary .partialDecrypt a b) ∧
    ¬ EqE ((world swap).eval (.binary .partialDecrypt a b)) (tallyPartial names swap left right [] 1) :=
  ⟨.of_nodeCount_one trivial rfl,
    expanded_minimum_partial_of_children names swap left right [] (by simp) (numeric swap) _ _
      (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl),
    expanded_constructed_partial_not_trustee_partial names swap left right [] (by simp)
      (.var (expandedPartial 0)) (.var (expandedResult 1)) trivial _⟩

/-- A successful structured-key E5 can return a published partial through a
nonminimum decryption wrapper. The origin theorem must keep its minimum premise. -/
theorem successful_decryption_needs_minimum_premise (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let b := keyCiphertext a (.name 60) (.var (expandedPartial 1))
    EqE ((world swap).eval (.binary .dec a b)) (tallyPartial names swap left right [] 1) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) ∧
    ¬ ((∃ c d : Recipe (ExpandedHandles 1), Term.binary .dec a b = .binary .partialDecrypt c d) ∨
      ∃ j : Fin 2, Term.binary .dec a b = .var (expandedPartial j)) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let b := keyCiphertext a (.name 60) (.var (expandedPartial 1))
  have hd : DecryptionMatch ((world swap).eval a) ((world swap).eval b)
      ((world swap).eval (.var (expandedPartial 1))) :=
    ⟨_,.name 60,Or.inl (.refl _),.refl _⟩
  refine ⟨?_,?_,?_⟩
  · simpa only [a,b,world,keyCiphertext,Frame.eval,Term.subst,expanded_frame_partial] using hd.reduces.sound
  · intro hm
    exact accepted_expanded_minimum_decryption_no_match names HistoricalFrameSPOT.fixture_names_fresh
      left right [] (by simp) trivial swap a b hm _ hd
  · rintro (⟨c,d,h⟩ | ⟨j,h⟩) <;> cases h

/-- The actual trustee E6 still matches; a whole recipe with that match is
excluded from minimum syntax by the general certificate proof. -/
theorem successful_E6_is_not_minimum (swap : Bool) :
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 1)
    let b := (tallyRecipe [] (1 : Fin 2)).subst (fun i => Term.var (expandedOld i))
    (∃ out, DecryptionMatch ((world swap).eval a) ((world swap).eval b) out) ∧
    ¬ MinimalRecipe names.restricted (world swap).value (.binary .dec a b) := by
  let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 1)
  let b := (tallyRecipe [] (1 : Fin 2)).subst (fun i => Term.var (expandedOld (n := 1) i))
  have hd : ∃ out, DecryptionMatch ((world swap).eval a) ((world swap).eval b) out := by
    change ∃ out, DecryptionMatch ((world swap).value (expandedPartial 1)) ((world swap).eval b) out
    rw [expanded_frame_partial,expanded_old_recipe_value]
    exact (TrusteePartialSPOT.both_candidates_match swap 1).1
  refine ⟨hd,?_⟩
  intro hm
  obtain ⟨out,hd⟩ := hd
  exact accepted_expanded_minimum_decryption_no_match names HistoricalFrameSPOT.fixture_names_fresh
    left right [] (by simp) trivial swap a b hm out hd

/-- Borrowed-slot equality closes at the one-node base case. The smaller-test
premise is empty at total size two, and the unequal bindings are retained. -/
theorem borrowed_partial_equality_transfer :
    (EqE ((world false).eval (.var (expandedPartial 0))) ((world false).eval (.var (expandedPartial 1))) ↔
      EqE ((world true).eval (.var (expandedPartial 0))) ((world true).eval (.var (expandedPartial 1)))) ∧
    ¬ EqE ((world false).eval (.var (expandedPartial 0))) ((world false).eval (.var (expandedPartial 1))) := by
  refine ⟨?_,?_⟩
  · apply expanded_minimum_partial_equality_swap names HistoricalFrameSPOT.fixture_names_fresh left right []
      (by simp) trivial (.var (expandedPartial 0)) (.var (expandedPartial 1))
      (.of_nodeCount_one trivial rfl) (.of_nodeCount_one trivial rfl)
      (key := .name names.secretKey) (binding := tallyCiphertext names false left right [] 0)
      (key' := .name names.secretKey) (binding' := tallyCiphertext names false left right [] 1)
    · simp only [Frame.eval,Term.subst,expanded_frame_partial]; exact .refl _
    · simp only [Frame.eval,Term.subst,expanded_frame_partial]; exact .refl _
    · intro r s _ _ hsize
      have hr := r.nodeCount_pos
      have hs := s.nodeCount_pos
      change r.nodeCount+s.nodeCount < 2 at hsize
      omega
  · simpa only [Frame.eval,Term.subst,expanded_frame_partial] using TrusteePartialSPOT.distinct_partial_slots.1

/-- The generic equality lemma now supports the expanded handle count. In a
diagonal election, constructed partials with unequal public names stay unequal. -/
theorem constructed_equality_transfer_nonconstant :
    let φ := expandedFrame names false left left []
    let ψ := expandedFrame names true left left []
    let a : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
    let r := Term.binary .partialDecrypt a (.name 40)
    let s := Term.binary .partialDecrypt a (.name 41)
    (EqE (φ.eval r) (φ.eval s) ↔ EqE (ψ.eval r) (ψ.eval s)) ∧ ¬ EqE (φ.eval r) (φ.eval s) := by
  refine ⟨partial_decryption_equality_transfer _ _ _ _ _ _ ?_ ?_ (fun _ _ _ _ _ => Iff.rfl),?_⟩
  · change True ∧ 40 ∉ names.restricted; decide
  · change True ∧ 41 ∉ names.restricted; decide
  · intro he
    exact absurd ((EqE.name_iff 40 41).mp ((EqE.partialDecrypt_iff _ _ _ _).mp he).2) (by decide)

/-- The direct published partial cannot be interpreted as an extractable pair
field under full E. This is the minimized opacity mutation control. -/
theorem partial_projection_cannot_expose_secret (swap : Bool) :
    ¬ EqE ((world swap).eval (.unary .fst (.var (expandedPartial 0)))) (.name names.secretKey) :=
  (expanded_frame_opaque_protected names swap left right [] (by simp)).name_not_deducible
    (.unary .fst (.var (expandedPartial 0))) trivial (by decide)

end ExplainableCrypto.Helios.Symbolic.ExpandedOriginSPOT
