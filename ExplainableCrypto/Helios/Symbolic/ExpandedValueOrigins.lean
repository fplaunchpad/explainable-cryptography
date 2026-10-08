import ExplainableCrypto.Helios.Symbolic.FrameMinimumOrigins
import ExplainableCrypto.Helios.Symbolic.ExpandedProjectionOrigins

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Both frame-specific premises of the generic induction are discharged from
actual expanded handles and their numeric result values. -/
theorem expanded_minimum_pair_and_ciphertext_origins (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) :
    MinimalRecipe restricted (expandedFrame ns swap left right rs).value r →
      (∀ x y, EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair x y) → PairRecipeOrigin r) ∧
      CiphertextCertificates (expandedFrame ns swap left right rs).value r :=
  (expandedFrame ns swap left right rs).minimum_pair_and_ciphertext_origins
    (expanded_handle_not_ciphertext ns swap left right rs hn)
    (fun _ hc => expanded_projection_chain_certificates ns swap left right rs hn hc) restricted r

theorem expanded_minimum_pair_origin (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {x y : Ground} (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .pair x y)) : PairRecipeOrigin r :=
  (expanded_minimum_pair_and_ciphertext_origins ns swap left right rs hn restricted r hm).1 x y he

/-- A certificate supplies actual public plaintext syntax, a strict size
bound and both semantic target components. It is not an assumed certificate. -/
theorem expanded_minimum_ciphertext_certificate (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    ∃ p s, CiphertextProduct (expandedFrame ns swap left right rs).value key r p s ∧
      p.Public restricted ∧ p.nodeCount < r.nodeCount ∧ EqE s nonce ∧
      EqE ((expandedFrame ns swap left right rs).eval p) message := by
  obtain ⟨p,s,hp,_⟩ := (expanded_minimum_pair_and_ciphertext_origins ns swap left right rs hn restricted r hm).2
    key nonce message he
  have hv := (EqE.penc_iff _ _ _ _ _ _).mp (hp.sound.symm.trans he)
  exact ⟨p,s,hp,hp.plaintext_public hm.isPublic,hp.plaintext_smaller,hv.2.1,hv.2.2⟩

theorem expanded_minimum_ciphertext_syntax (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (r : Recipe (ExpandedHandles n)) (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r)
    {key nonce message : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.ternary .penc key nonce message)) :
    CiphertextRecipeSyntax r := by
  obtain ⟨_,_,_,hs⟩ := (expanded_minimum_pair_and_ciphertext_origins ns swap left right rs hn restricted r hm).2
    key nonce message he
  exact hs

/-- Both E5 and E6 matches would reveal a strictly smaller public plaintext
recipe. Only a whole minimum decryption is excluded; ordinary decryption works. -/
theorem expanded_minimum_decryption_no_match (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat)
    (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (out : Ground) :
    ¬ DecryptionMatch ((expandedFrame ns swap left right rs).eval a) ((expandedFrame ns swap left right rs).eval b) out :=
  hm.no_decryption_match_of_certificates
    (expanded_minimum_pair_and_ciphertext_origins ns swap left right rs hn restricted b
      (hm.subterm (.binaryRight .dec a .hole))).2 out

/-- The full minimum partial-valued class in the expanded frame consists of
public constructors and borrowed partial slots, including arbitrary target keys
and bindings. Successful decryption and hidden projection origins are excluded. -/
theorem expanded_minimum_partial_decryption_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hn : ExpandedResultsNumeric ns swap left right rs) (restricted : Finset Nat) (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe restricted (expandedFrame ns swap left right rs).value r) {k c : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .partialDecrypt k c)) :
    (∃ a b, r = .binary .partialDecrypt a b) ∨
      ∃ j : Fin (n+1), r = .var (expandedPartial j) := by
  cases r with
  | name a =>
    obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (name_irreducible a)
    cases hshape
  | const d =>
    obtain ⟨_, _, hshape, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inr rfl) (constant_irreducible d)
    cases hshape
  | var v => exact Or.inr (expanded_projection_partial_origin ns swap left right rs hn v .handle he)
  | unary f a =>
    have reject (hf : f = .fst ∨ f = .snd) : False := by
      obtain ⟨x, y, hp, _⟩ := he.projection_partialDecrypt_inversion hf
      have horigin := expanded_minimum_pair_origin ns swap left right rs hn restricted a
        (hm.subterm (.unary f .hole)) hp.sound
      obtain ⟨v, hc⟩ := hm.projection_chain_of_pair_origin hf horigin
      obtain ⟨j,hj⟩ := expanded_projection_partial_origin ns swap left right rs hn v hc he
      cases hj
    cases f with
    | pk => exact False.elim (pk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ he)
    | fst => exact False.elim (reject (Or.inl rfl))
    | snd => exact False.elim (reject (Or.inr rfl))
  | binary f a b =>
    cases f with
    | partialDecrypt => exact Or.inl ⟨a, b, rfl⟩
    | pair =>
      have hf := ((EqE.passive_binary_iff .pair .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _).mp he).1
      cases hf
    | mul => exact False.elim (mul_not_eqE_passive_binary _ _ _ _ .partialDecrypt (Or.inr rfl) he)
    | add =>
      exact False.elim
        (arithmetic_not_eqE_passive_binary .add .partialDecrypt (Or.inl rfl) (Or.inr rfl) _ _ _ _ he)
    | compose =>
      exact False.elim
        (arithmetic_not_eqE_passive_binary .compose .partialDecrypt (Or.inr rfl) (Or.inr rfl) _ _ _ _ he)
    | dec =>
      obtain ⟨out, hd, _⟩ := he.decryption_partialDecrypt_inversion
      exact False.elim (expanded_minimum_decryption_no_match ns swap left right rs hn restricted a b hm out hd)
  | ternary f a b d =>
    cases f with
    | penc => exact False.elim (penc_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he)
    | checkspk => exact False.elim (proof_check_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ he)
  | spk a b d e => exact False.elim (spk_not_eqE_passive_binary .partialDecrypt (Or.inr rfl) _ _ _ _ _ _ he)

/-- Actual accepted elections discharge the numeric-result premise of the
full constructed-or-borrowed partial-value origin theorem. -/
theorem accepted_expanded_minimum_partial_form (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (swap : Bool) (r : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value r) {key binding : Ground}
    (he : EqE ((expandedFrame ns swap left right rs).eval r) (.binary .partialDecrypt key binding)) :
    (∃ a b, r = .binary .partialDecrypt a b) ∨ ∃ j : Fin (n+1), r = .var (expandedPartial j) :=
  expanded_minimum_partial_decryption_form ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted r hm he

/-- This excludes matches of the whole minimum recipe in either accepted
world, without assuming any ciphertext-origin certificate from the caller. -/
theorem accepted_expanded_minimum_decryption_no_match (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (swap : Bool) (a b : Recipe (ExpandedHandles n))
    (hm : MinimalRecipe ns.restricted (expandedFrame ns swap left right rs).value (.binary .dec a b))
    (out : Ground) :
    ¬ DecryptionMatch ((expandedFrame ns swap left right rs).eval a) ((expandedFrame ns swap left right rs).eval b) out :=
  expanded_minimum_decryption_no_match ns swap left right rs
    (accepted_expanded_results_numeric ns hf left right rs hp ha swap) ns.restricted a b hm out

end ExplainableCrypto.Helios.Symbolic.Historical.General
