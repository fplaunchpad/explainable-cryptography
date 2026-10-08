import ExplainableCrypto.Helios.Symbolic.PartialKeyObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- Existence of a pair E-value; the supplied term need not be normal. -/
def Term.PairValue (t : Term V) : Prop := ∃ a b, EqE t (.binary .pair a b)
/-- Existence of a ciphertext E-value with arbitrary key, nonce and plaintext. -/
def Term.CiphertextValue (t : Term V) : Prop := ∃ k r m, EqE t (.ternary .penc k r m)
/-- Existence of an ordered partial-decryption constructor E-value. -/
def Term.PartialValue (t : Term V) : Prop := ∃ k c, EqE t (.binary .partialDecrypt k c)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Initial handle chains have the same pair/ciphertext/partial value classes
in either assignment. This statement needs neither minimum size nor public
observation hypotheses; exact tuple positions determine these classes. -/
theorem projection_chain_shape_reflection (ns : Names n) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (v : Fin 3) {r : Recipe 3}
    (hc : ProjectionChain v r) :
    (((frame ns swap' left right).eval r).PairValue → ((frame ns swap left right).eval r).PairValue) ∧
    (((frame ns swap' left right).eval r).CiphertextValue → ((frame ns swap left right).eval r).CiphertextValue) ∧
    (((frame ns swap' left right).eval r).PartialValue → ((frame ns swap left right).eval r).PartialValue) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, b, he⟩
    obtain ⟨i, k, hk, rfl⟩ := frame_projection_pair_origin ns swap' left right v hc he
    exact ballot_tail_pair_value ns swap left right i k hk
  · rintro ⟨k, nonce, p, he⟩
    obtain ⟨i, j, _, rfl, _⟩ := frame_projection_ciphertext_origin ns swap' left right v hc he
    refine ⟨publicKey ns, .name (ns.nonce i j), (choice swap left right i).value j, ?_⟩
    simpa only [Frame.eval, Term.subst_project, Term.subst, frame_voter_handle, ciphertext] using
      ballot_project_ciphertext ns i (choice swap left right i).value j
  · rintro ⟨k, c, he⟩
    exact False.elim (frame_projection_not_partialDecrypt ns swap' left right v hc k c he)

/-- A source minimum ciphertext value has assembly syntax and remains a
ciphertext when its smaller key-coherence observations are preserved. -/
theorem minimum_ciphertext_value_forward (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right) r.nodeCount)
    (hv : ((frame ns false left right).eval r).CiphertextValue) :
    ((frame ns true left right).eval r).CiphertextValue := by
  obtain ⟨k, nonce, p, he⟩ := hv
  obtain ⟨t, rfl, hk, _⟩ := minimum_ciphertext_grouping ns false left right ns.restricted r hm he
  have hc := t.coherent_of_key_agreement ns false left right k hk
  have hc' := (t.coherent_transfer _ _ hm.isPublic hobs).mp hc
  exact (t.coherent_iff_ciphertext_value ns true left right).mp hc'

/-- Pair and partial constructor values of source minima have exact raw origins
whose value classes survive the swap without an observation premise. -/
theorem minimum_passive_values_forward (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value r) :
    (((frame ns false left right).eval r).PairValue → ((frame ns true left right).eval r).PairValue) ∧
    (((frame ns false left right).eval r).PartialValue → ((frame ns true left right).eval r).PartialValue) := by
  constructor
  · rintro ⟨a, b, he⟩
    rcases minimum_pair_observation_form ns false left right ns.restricted r hm he with
      ⟨a, b, rfl⟩ | ⟨i, k, hk, rfl⟩
    · exact ⟨_, _, .refl _⟩
    · exact ballot_tail_pair_value ns true left right i k hk
  · rintro ⟨k, c, he⟩
    obtain ⟨a, b, rfl⟩ := minimum_partial_decryption_form ns false left right ns.restricted r hm he
    exact ⟨_, _, .refl _⟩

/-- The structural induction needs only ciphertext reflection for the second
argument and partial-value reflection for the first. Every destination E5/E6
match then contradicts source minimum size through smaller public probes. -/
theorem minimum_decryption_failure_of_reflection (ns : Names n)
    (left right : CandidateSubstitution n Empty) (a b : Recipe 3)
    (hm : MinimalRecipe ns.restricted (frame ns false left right).value (.binary .dec a b))
    (ha : ((frame ns true left right).eval a).PartialValue → ((frame ns false left right).eval a).PartialValue)
    (hb : ((frame ns true left right).eval b).CiphertextValue → ((frame ns false left right).eval b).CiphertextValue)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (Term.binary .dec a b).nodeCount) :
    ∀ m, ¬ DecryptionMatch ((frame ns true left right).eval a) ((frame ns true left right).eval b) m := by
  intro m hmatch
  obtain ⟨k, nonce, hk, hc⟩ := hmatch
  obtain ⟨key, rand, p, hvalue⟩ := hb ⟨_, _, _, hc.sound⟩
  rcases hk with hk | hk
  · obtain ⟨t, rfl, hkeys, _⟩ := minimum_ciphertext_grouping ns false left right ns.restricted b
      (hm.subterm (.binaryRight .dec a .hole)) hvalue
    have hcoh := t.coherent_of_key_agreement ns false left right key hkeys
    have hcoh' := (t.coherent_transfer _ _ hm.isPublic.2
      (hobs.mono (by simp only [Term.nodeCount]; omega))).mp hcoh
    have hval := t.grouped_value ns false left right _ (t.key_agreement_of_coherent ns false left right hcoh)
    have hval' := t.grouped_value ns true left right _ (t.key_agreement_of_coherent ns true left right hcoh')
    have hkey' := ((EqE.penc_iff _ _ _ _ _ _).mp (hval'.symm.trans hc.sound)).1
    have hprobe' := hkey'.trans (.unary .pk hk.sound.symm)
    have hprobe := (hobs t.keyRecipe (.unary .pk a) (t.keyRecipe_public hm.isPublic.2) hm.isPublic.1 (by
      have := t.keyRecipe_smaller
      simp only [Term.nodeCount]; omega)).mpr hprobe'
    obtain ⟨out, hout⟩ := DecryptionMatch.exists_of_values
      (hval.trans (.ternary .penc hprobe (.refl _) (.refl _))) (Or.inl (.refl _))
    exact minimum_decryption_no_match ns false left right ns.restricted a t.recipe hm out hout
  · obtain ⟨ak, ac, hpart⟩ := ha ⟨_, _, hk.sound⟩
    exact minimum_partial_key_decryption_failure ns left right a b hm hpart hvalue hobs m
      ⟨k, nonce, Or.inr hk, hc⟩

end ExplainableCrypto.Helios.Symbolic.Historical.General
