import ExplainableCrypto.Helios.Symbolic.HonestProofEquality

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {handles : Nat}

/-- Every component, including the fourth bound-ciphertext argument, is a
strictly smaller public observation for two constructed proofs. -/
theorem constructed_proof_equality_transfer (φ ψ : Frame restricted handles)
    (a b c d a' b' c' d' : Recipe handles)
    (hp : (Term.spk a b c d).Public restricted) (hq : (Term.spk a' b' c' d').Public restricted)
    (hobs : φ.ObservationsBelow ψ
      ((Term.spk a b c d).nodeCount + (Term.spk a' b' c' d').nodeCount)) :
    EqE (φ.eval (.spk a b c d)) (φ.eval (.spk a' b' c' d')) ↔
      EqE (ψ.eval (.spk a b c d)) (ψ.eval (.spk a' b' c' d')) := by
  have ha := hobs a a' hp.1 hq.1 (by simp only [Term.nodeCount]; omega)
  have hb := hobs b b' hp.2.1 hq.2.1 (by simp only [Term.nodeCount]; omega)
  have hc := hobs c c' hp.2.2.1 hq.2.2.1 (by simp only [Term.nodeCount]; omega)
  have hd := hobs d d' hp.2.2.2 hq.2.2.2 (by simp only [Term.nodeCount]; omega)
  exact (EqE.spk_iff _ _ _ _ _ _ _ _).trans
    ((and_congr ha (and_congr hb (and_congr hc hd))).trans (EqE.spk_iff _ _ _ _ _ _ _ _).symm)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem test_transport {a b x y : Ground} (ha : EqE a x) (hb : EqE b y) :
    EqE a b ↔ EqE x y :=
  ⟨fun h => ha.symm.trans (h.trans hb), fun h => ha.trans (h.trans hb.symm)⟩

/-- All constructed/component/aggregate proof-form comparisons transfer from
smaller public tests. Honest-only criteria depend on nonce provenance and keep
the component/aggregate equality at the single-candidate boundary. -/
theorem proof_form_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : r.Public ns.restricted) (hs : s.Public ns.restricted)
    (hfr : ProofRecipeForm n r) (hfs : ProofRecipeForm n s)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  have hpolicy : ns.nonceNames ⊆ ns.restricted := fun _ h => Finset.mem_union_right _ h
  have hr' := hr.of_subset hpolicy
  have hs' := hs.of_subset hpolicy
  rcases hfr with ⟨a, b, c, d, rfl⟩ | ⟨i, j, rfl⟩ | ⟨i, rfl⟩
  · rcases hfs with ⟨a', b', c', d', rfl⟩ | ⟨k, l, rfl⟩ | ⟨k, rfl⟩
    · exact constructed_proof_equality_transfer _ _ a b c d a' b' c' d' hr hs hobs
    · have reject (swap : Bool) :
          ¬ EqE ((frame ns swap left right).eval (.spk a b c d))
            ((frame ns swap left right).eval ((Term.var k.succ).project (n + 1 + l.val))) := by
        intro he
        exact constructed_proof_not_component ns swap left right a b c d hr'.2.1 k l
          (he.trans (component_proof_recipe_value ns swap left right k l))
      exact iff_of_false (reject false) (reject true)
    · have reject (swap : Bool) :
          ¬ EqE ((frame ns swap left right).eval (.spk a b c d))
            ((frame ns swap left right).eval ((Term.var k.succ).project (2 * (n + 1)))) := by
        intro he
        exact constructed_proof_not_aggregate ns swap left right a b c d hr'.2.1 k
          (he.trans (aggregate_proof_recipe_value ns swap left right k))
      exact iff_of_false (reject false) (reject true)
  · rcases hfs with ⟨a', b', c', d', rfl⟩ | ⟨k, l, rfl⟩ | ⟨k, rfl⟩
    · have reject (swap : Bool) :
          ¬ EqE ((frame ns swap left right).eval ((Term.var i.succ).project (n + 1 + j.val)))
            ((frame ns swap left right).eval (.spk a' b' c' d')) := by
        intro he
        exact constructed_proof_not_component ns swap left right a' b' c' d' hs'.2.1 i j
          (he.symm.trans (component_proof_recipe_value ns swap left right i j))
      exact iff_of_false (reject false) (reject true)
    · have criterion (swap : Bool) :
          EqE ((frame ns swap left right).eval ((Term.var i.succ).project (n + 1 + j.val)))
            ((frame ns swap left right).eval ((Term.var k.succ).project (n + 1 + l.val))) ↔ i = k ∧ j = l :=
        (test_transport (component_proof_recipe_value ns swap left right i j)
          (component_proof_recipe_value ns swap left right k l)).trans
          (component_proof_equality_iff ns hf swap left right i k j l)
      exact (criterion false).trans (criterion true).symm
    · have criterion (swap : Bool) :
          EqE ((frame ns swap left right).eval ((Term.var i.succ).project (n + 1 + j.val)))
            ((frame ns swap left right).eval ((Term.var k.succ).project (2 * (n + 1)))) ↔ n = 0 ∧ i = k :=
        (test_transport (component_proof_recipe_value ns swap left right i j)
          (aggregate_proof_recipe_value ns swap left right k)).trans
          (component_aggregate_proof_equality_iff ns hf swap left right i k j)
      exact (criterion false).trans (criterion true).symm
  · rcases hfs with ⟨a', b', c', d', rfl⟩ | ⟨k, l, rfl⟩ | ⟨k, rfl⟩
    · have reject (swap : Bool) :
          ¬ EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
            ((frame ns swap left right).eval (.spk a' b' c' d')) := by
        intro he
        exact constructed_proof_not_aggregate ns swap left right a' b' c' d' hs'.2.1 i
          (he.symm.trans (aggregate_proof_recipe_value ns swap left right i))
      exact iff_of_false (reject false) (reject true)
    · have criterion (swap : Bool) :
          EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
            ((frame ns swap left right).eval ((Term.var k.succ).project (n + 1 + l.val))) ↔ n = 0 ∧ k = i :=
        (test_transport (aggregate_proof_recipe_value ns swap left right i)
          (component_proof_recipe_value ns swap left right k l)).trans
          ((show (EqE (aggregateProof ns i (choice swap left right i).value)
              (componentProof ns k (choice swap left right k).value l) ↔
            EqE (componentProof ns k (choice swap left right k).value l)
              (aggregateProof ns i (choice swap left right i).value)) from ⟨EqE.symm, EqE.symm⟩).trans
            (component_aggregate_proof_equality_iff ns hf swap left right k i l))
      exact (criterion false).trans (criterion true).symm
    · have criterion (swap : Bool) :
          EqE ((frame ns swap left right).eval ((Term.var i.succ).project (2 * (n + 1))))
            ((frame ns swap left right).eval ((Term.var k.succ).project (2 * (n + 1)))) ↔ i = k :=
        (test_transport (aggregate_proof_recipe_value ns swap left right i)
          (aggregate_proof_recipe_value ns swap left right k)).trans
          (aggregate_proof_equality_iff ns hf swap left right i k)
      exact (criterion false).trans (criterion true).symm

/-- The proof-valued minimum-recipe branch derives both exact proof forms from
first-world values. No second-world origin, minimum or value premise is assumed. -/
theorem minimum_proof_equality_swap (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {a b c d a' b' c' d' : Ground}
    (her : EqE ((frame ns false left right).eval r) (.spk a b c d))
    (hes : EqE ((frame ns false left right).eval s) (.spk a' b' c' d'))
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) :=
  proof_form_equality_swap ns hf left right r s hr.isPublic hs.isPublic
    (minimum_proof_form ns false left right ns.restricted r hr her)
    (minimum_proof_form ns false left right ns.restricted s hs hes) hobs

end ExplainableCrypto.Helios.Symbolic.Historical.General
