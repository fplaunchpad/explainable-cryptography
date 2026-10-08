import ExplainableCrypto.Helios.Symbolic.PublicKeyMinimumTools

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Exact minimum key-valued syntax in the initial frame. -/
def PublicKeyRecipeForm (r : Recipe 3) : Prop := r = .var 0 ∨ ∃ a, r = .unary .pk a

/-- Public-key-valued minimum recipes are constructed keys or the election-key
handle. Arbitrary supplied key values may contain reducible components. -/
theorem minimum_public_key_form (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (r : Recipe 3)
    (hm : MinimalRecipe restricted (frame ns swap left right).value r) {k : Ground}
    (he : EqE ((frame ns swap left right).eval r) (.unary .pk k)) : PublicKeyRecipeForm r :=
  (frame ns swap left right).minimum_public_key_form_of_origins restricted 0
    (fun r hm _ _ he => minimum_pair_origin ns swap left right restricted r hm he)
    (fun a b hm out => minimum_decryption_no_match ns swap left right restricted a b hm out)
    (fun v _ hc _ he => frame_projection_pk_origin ns swap left right v hc he) r hm he

/-- The full public-name restriction excludes the trustee secret key. This
argument is about deducibility, not a count or a failed search. -/
theorem frame_secret_key_not_deducible (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval r) (.name ns.secretKey) :=
  frame_nonce_not_deducible ns swap left right r hr (by simp [Names.restricted])

theorem constructed_key_not_election_key (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (hr : r.Public ns.restricted) :
    ¬ EqE ((frame ns swap left right).eval (.unary .pk r)) (publicKey ns) := by
  intro he
  exact frame_secret_key_not_deducible ns swap left right r hr ((EqE.pk_iff _ _).mp he)

/-- The published handle is the only minimum full-policy recipe for the exact
election public key. This does not classify arbitrary nonminimum wrappers. -/
theorem minimum_election_key_handle (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns swap left right).value r)
    (he : EqE ((frame ns swap left right).eval r) (publicKey ns)) : r = .var 0 := by
  rcases minimum_public_key_form ns swap left right ns.restricted r hm he with hr | ⟨a, rfl⟩
  · exact hr
  · exact False.elim (constructed_key_not_election_key ns swap left right a hm.isPublic he)

/-- The four form comparisons retain election-handle equality, exclude public
reconstruction of that key, and reduce two constructed keys to smaller arguments. -/
theorem public_key_form_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : PublicKeyRecipeForm r) (hfs : PublicKeyRecipeForm s)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  rcases hfr with rfl | ⟨a, rfl⟩
  · rcases hfs with rfl | ⟨b, rfl⟩
    · exact Iff.rfl
    · exact iff_of_false
        (fun he => constructed_key_not_election_key ns false left right b hs he.symm)
        (fun he => constructed_key_not_election_key ns true left right b hs he.symm)
  · rcases hfs with rfl | ⟨b, rfl⟩
    · exact iff_of_false (constructed_key_not_election_key ns false left right a hr)
        (constructed_key_not_election_key ns true left right a hr)
    · have h := hobs a b hr hs (by simp only [Term.nodeCount]; omega)
      exact (EqE.pk_iff _ _).trans (h.trans (EqE.pk_iff _ _).symm)

/-- The public-key-valued minimum branch derives both forms from first-world
values. Fresh nonce labels are unnecessary for this branch; the full secret-name
policy and smaller-observation hypothesis remain explicit. -/
theorem minimum_public_key_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {k l : Ground}
    (her : EqE ((frame ns false left right).eval r) (.unary .pk k))
    (hes : EqE ((frame ns false left right).eval s) (.unary .pk l))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) :=
  public_key_form_equality_swap ns left right r s hr.isPublic hs.isPublic
    (minimum_public_key_form ns false left right ns.restricted r hr her)
    (minimum_public_key_form ns false left right ns.restricted s hs hes) hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
