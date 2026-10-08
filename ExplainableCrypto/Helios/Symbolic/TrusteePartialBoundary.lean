import ExplainableCrypto.Helios.Symbolic.PublishedResults

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Before publication, the key of a ciphertext cannot be the public key of
an election-secret partial. Public-key origins would expose that partial. -/
theorem initial_trustee_partial_key_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (binding : Ground)
    (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r)
      (.unary .pk (.binary .partialDecrypt (.name ns.secretKey) binding)) := by
  intro he
  obtain ⟨m,hm,hmin⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) r hr
  have hk := hmin.symm.trans he
  rcases minimum_public_key_form ns swap left right ns.restricted m hm hk with rfl | ⟨a,rfl⟩
  · have hs := (EqE.pk_iff _ _).mp hk
    obtain ⟨_,_,hshape,_⟩ := hs.symm.passive_binary_irreducible_shape
      (Or.inr rfl) (name_irreducible ns.secretKey)
    cases hshape
  · exact initial_secret_partial_not_deducible ns swap left right binding a hm.isPublic
      ((EqE.pk_iff _ _).mp hk)

/-- This exclusion is specific to the initial public frame. After publication,
an attacker can construct ciphertexts under the partial's public key. -/
theorem initial_ciphertext_not_keyed_by_trustee_partial (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (binding nonce p : Ground)
    (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r)
      (keyCiphertext (.binary .partialDecrypt (.name ns.secretKey) binding) nonce p) := by
  intro he
  obtain ⟨m,hm,hmin⟩ := exists_minimal_recipe (σ := (frame ns swap left right).value) r hr
  obtain ⟨t,_,_,_,_,ht,_,hk,_⟩ :=
    minimum_ciphertext_grouping ns swap left right ns.restricted m hm (hmin.symm.trans he)
  exact initial_trustee_partial_key_not_deducible ns swap left right binding t.keyRecipe ht hk

/-- When a trustee partial meets an old public recipe, the E5 branch is
impossible. E6 matches exactly the whole election-ciphertext binding. -/
theorem initial_trustee_partial_match_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (binding nonce p : Ground)
    (hb : EqE binding (.ternary .penc (publicKey ns) nonce p))
    (r : Recipe 3) (hr : r.Public ns.restricted) :
    (∃ m, DecryptionMatch (.binary .partialDecrypt (.name ns.secretKey) binding)
      ((frame ns swap left right).eval r) m) ↔
    EqE ((frame ns swap left right).eval r) binding := by
  constructor
  · intro h
    obtain ⟨k,nr,out,hc,hk⟩ := (DecryptionMatch.exists_iff_values _ _).mp h
    rcases hk with hk | hk
    · exact False.elim (initial_ciphertext_not_keyed_by_trustee_partial ns swap left right binding nr out r hr
        (hc.trans (.ternary .penc (.unary .pk hk.symm) (.refl _) (.refl _))))
    · exact ((EqE.partialDecrypt_iff _ _ _ _).mp hk).2.symm
  · intro he
    exact DecryptionMatch.exists_of_values (he.trans hb)
      (Or.inr (.binary .partialDecrypt (.refl _) he.symm))

/-- Equality of trustee partials is exactly equality of their complete bindings. -/
theorem tally_partial_eq_iff (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3)) (i j : Fin (n+1)) :
    EqE (tallyPartial ns swap left right rs i) (tallyPartial ns swap left right rs j) ↔
    EqE (tallyCiphertext ns swap left right rs i) (tallyCiphertext ns swap left right rs j) := by
  exact (EqE.partialDecrypt_iff _ _ _ _).trans (and_iff_right (.refl _))

/-- The equality pattern among partial slots transfers through the old public
aggregate recipes. This does not cover arbitrary new-frame observations. -/
theorem tally_partial_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted) (i j : Fin (n+1)) :
    EqE (tallyPartial ns false left right rs i) (tallyPartial ns false left right rs j) ↔
    EqE (tallyPartial ns true left right rs i) (tallyPartial ns true left right rs j) :=
  (tally_partial_eq_iff ns false left right rs i j).trans
    (((initial_frame_staticEq ns hf left right) (tallyRecipe rs i) (tallyRecipe rs j)
      (tallyRecipe_public rs i ns.restricted hp) (tallyRecipe_public rs j ns.restricted hp)).trans
        (tally_partial_eq_iff ns true left right rs i j).symm)

/-- Acceptance supplies the election-ciphertext shape for each actual tally.
The equivalence quantifies over every initial public recipe. -/
theorem accepted_tally_partial_match_iff (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (swap : Bool) (j : Fin (n+1)) (r : Recipe 3) (hr : r.Public ns.restricted) :
    (∃ m, DecryptionMatch (tallyPartial ns swap left right rs j)
      ((frame ns swap left right).eval r) m) ↔
    EqE ((frame ns swap left right).eval r) (tallyCiphertext ns swap left right rs j) := by
  have hb : ∀ i : Fin 2, (Term.var i.succ : Recipe 3) ∈ honestBoardRecipes := by
    intro i
    fin_cases i <;> simp [honestBoardRecipes]
  obtain ⟨ds,hds⟩ := accepted_sequence_common_data ns hf left right honestBoardRecipes rs hb hp ha
  exact initial_trustee_partial_match_iff ns swap left right _ _ _
    (tally_ciphertext_of_common_data ns swap left right rs ds hds j) r hr

/-- Every old-public-recipe match with an actual partial transfers across the
vote swap. The extended frame's arbitrary nested recipes remain a separate goal. -/
theorem accepted_tally_partial_match_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) (r : Recipe 3) (hr : r.Public ns.restricted) :
    (∃ m, DecryptionMatch (tallyPartial ns false left right rs j)
      ((frame ns false left right).eval r) m) ↔
    (∃ m, DecryptionMatch (tallyPartial ns true left right rs j)
      ((frame ns true left right).eval r) m) :=
  (accepted_tally_partial_match_iff ns hf left right rs hp ha false j r hr).trans
    (((initial_frame_staticEq ns hf left right) r (tallyRecipe rs j) hr
      (tallyRecipe_public rs j ns.restricted hp)).trans
        (accepted_tally_partial_match_iff ns hf left right rs hp ha true j r hr).symm)

/-- A successful boundary match computes the actual tally result, rather than
merely an unspecified value shared by the two frames. -/
theorem accepted_tally_partial_decryption_value (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (swap : Bool) (j : Fin (n+1)) (r : Recipe 3) (hr : r.Public ns.restricted)
    (h : ∃ m, DecryptionMatch (tallyPartial ns swap left right rs j)
      ((frame ns swap left right).eval r) m) :
    EqE (.binary .dec (tallyPartial ns swap left right rs j) ((frame ns swap left right).eval r))
      (tallyResult ns swap left right rs j) :=
  .binary .dec (.refl _) ((accepted_tally_partial_match_iff ns hf left right rs hp ha swap j r hr).mp h)

/-- Actual public probes made from one partial projection and an old public
recipe return one bounded numeral in both worlds whenever the source matches. -/
theorem accepted_tally_partial_probe_numeric (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (rs : List (Recipe 3))
    (hp : ∀ r ∈ rs, r.Public ns.restricted)
    (ha : (frame ns false left right).AcceptsSequence n (.var 0) honestBoardRecipes rs)
    (j : Fin (n+1)) (r : Recipe 3) (hr : r.Public ns.restricted)
    (h : ∃ m, DecryptionMatch (tallyPartial ns false left right rs j)
      ((frame ns false left right).eval r) m) :
    ∃ k, k ≤ rs.length+2 ∧ ∀ swap : Bool,
      EqE ((partialFrame ns swap left right rs).eval
        (.binary .dec ((Term.var 3).project j.val) r.lift)) (addNumeral k) := by
  obtain ⟨k,hk,ht⟩ := accepted_sequence_tally_numeric ns hf left right rs hp ha j
  refine ⟨k,hk,?_⟩
  intro swap
  have hm : ∃ m, DecryptionMatch (tallyPartial ns swap left right rs j)
      ((frame ns swap left right).eval r) m := by
    cases swap with
    | false => exact h
    | true => exact (accepted_tally_partial_match_swap ns hf left right rs hp ha j r hr).mp h
  have hv := accepted_tally_partial_decryption_value ns hf left right rs hp ha swap j r hr hm
  have hl := Frame.eval_extend_lift (frame ns swap left right) (candidateTuple (tallyPartial ns swap left right rs)) r
  exact (EqE.binary .dec (partialFrame_partial_project ns swap left right rs j)
    (hl ▸ EqE.refl _)).trans (hv.trans (ht swap))

end ExplainableCrypto.Helios.Symbolic.Historical.General
