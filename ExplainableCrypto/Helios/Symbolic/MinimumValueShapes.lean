import ExplainableCrypto.Helios.Symbolic.FrameValueShapeReflection

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Simultaneous reflection derives source constructor values from destination
values. Source minimum size and observations below this recipe suffice; no
minimum-size or constructor-value hypothesis is assumed in the destination. -/
theorem minimum_value_shape_reflection (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) :
    MinimalRecipe ns.restricted (frame ns false left right).value r →
    (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount →
    ((((frame ns true left right).eval r).PairValue → ((frame ns false left right).eval r).PairValue) ∧
      (((frame ns true left right).eval r).CiphertextValue → ((frame ns false left right).eval r).CiphertextValue) ∧
      (((frame ns true left right).eval r).PartialValue → ((frame ns false left right).eval r).PartialValue)) := by
  apply Frame.minimum_value_shape_reflection_of_cases (frame ns false left right) (frame ns true left right)
    (fun v _ hc => projection_chain_shape_reflection ns false true left right v hc)
    (fun r hm _ _ he => minimum_pair_origin ns false left right ns.restricted r hm he)
  · intro a b hm ha hb hobs
    rintro ⟨key, nonce, p, he⟩
    obtain ⟨ra, rb, ma, mb, hea, heb, _⟩ := he.mul_penc_inversion
    obtain ⟨ka, na, pa, hsourcea⟩ := ha ⟨key, ra, ma, hea⟩
    obtain ⟨kb, nb, pb, hsourceb⟩ := hb ⟨key, rb, mb, heb⟩
    obtain ⟨ta, rfl, _⟩ := minimum_ciphertext_grouping ns false left right ns.restricted a
      (hm.subterm (.binaryLeft .mul .hole b)) hsourcea
    obtain ⟨tb, rfl, _⟩ := minimum_ciphertext_grouping ns false left right ns.restricted b
      (hm.subterm (.binaryRight .mul ta.recipe .hole)) hsourceb
    let t := CiphertextAssembly.mul ta tb
    have hc' := t.coherent_of_key_agreement ns true left right key (t.key_agreement_of_value ns true left right he)
    have hc := (t.coherent_transfer _ _ hm.isPublic hobs).mpr hc'
    exact (t.coherent_iff_ciphertext_value ns false left right).mp hc
  · intro a b hm ha hb hobs out hmatch
    exact False.elim (minimum_decryption_failure_of_reflection ns left right a b hm ha hb hobs out hmatch)

/-- Pair, ciphertext and partial constructor value classes are invariant for a
source minimum recipe under observations strictly below its own syntax size. -/
theorem minimum_value_shapes_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount) :
    (((frame ns false left right).eval r).PairValue ↔ ((frame ns true left right).eval r).PairValue) ∧
    (((frame ns false left right).eval r).CiphertextValue ↔ ((frame ns true left right).eval r).CiphertextValue) ∧
    (((frame ns false left right).eval r).PartialValue ↔ ((frame ns true left right).eval r).PartialValue) := by
  have href := minimum_value_shape_reflection ns left right r hm hobs
  have hf := minimum_passive_values_forward ns left right r hm
  exact ⟨⟨hf.1, href.1⟩, ⟨minimum_ciphertext_value_forward ns left right r hm hobs, href.2.1⟩,
    ⟨hf.2, href.2.2⟩⟩

/-- Every minimum initial-frame decryption stays unmatched in the destination.
No source argument-shape certificates remain in the public premises. -/
theorem minimum_decryption_failure_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec a b))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (Term.binary .dec a b).nodeCount) :
    ∀ m, ¬ DecryptionMatch ((frame ns true left right).eval a) ((frame ns true left right).eval b) m := by
  have ha := minimum_value_shape_reflection ns left right a (hm.subterm (.binaryLeft .dec .hole b))
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  have hb := minimum_value_shape_reflection ns left right b (hm.subterm (.binaryRight .dec a .hole))
    (hobs.mono (by simp only [Term.nodeCount]; omega))
  exact minimum_decryption_failure_of_reflection ns left right a b hm ha.2.2 hb.2.1 hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
