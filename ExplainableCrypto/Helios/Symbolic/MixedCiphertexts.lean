import ExplainableCrypto.Helios.Symbolic.MixedNonceProvenance

namespace ExplainableCrypto.Helios.Symbolic
variable {V α : Type}

/-- A present numeric value can be replaced by zero in a common-offset equality
comparison. The common value may be reducible and may denote zero. -/
theorem EqE.add_numeric_value_iff_zero (p q m : Term V)
    (hm : ∃ k : Nat, EqE m (addNumeral k)) :
    EqE (.binary .add p m) (.binary .add q m) ↔
      EqE (.binary .add p (.const .zero)) (.binary .add q (.const .zero)) := by
  obtain ⟨k, hk⟩ := hm
  have hp := EqE.binary .add (EqE.refl p) hk
  have hq := EqE.binary .add (EqE.refl q) hk
  have h : EqE (.binary .add p m) (.binary .add q m) ↔
      EqE (.binary .add p (addNumeral k)) (.binary .add q (addNumeral k)) :=
    ⟨fun he => hp.symm.trans (he.trans hq), fun he => hp.trans (he.trans hq.symm)⟩
  exact h.trans (EqE.add_numeric_offset_iff p q k 0)

theorem Combination.exists_index (t : Combination α) : ∃ i, i ∈ t.indices := by
  induction t with
  | leaf i => exact ⟨i, by simp [Combination.indices]⟩
  | mul a b ia _ =>
    obtain ⟨i, hi⟩ := ia
    exact ⟨i, Multiset.mem_add.mpr (Or.inl hi)⟩

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Publicly constructed ciphertext times a nonempty honest ciphertext product. -/
def mixedCombinationRecipe (r p : Recipe 3) (t : Combination (HonestIndex n)) : Recipe 3 :=
  .binary .mul (.ternary .penc (.var 0) r p) (combinationRecipe t)

theorem mixedCombination_public {restricted : Finset Nat} (r p : Recipe 3)
    (hr : r.Public restricted) (hp : p.Public restricted) (t : Combination (HonestIndex n)) :
    (mixedCombinationRecipe r p t).Public restricted :=
  ⟨⟨trivial, hr, hp⟩, combinationRecipe_public restricted t⟩

theorem mixedCombination_value (ns : Names n) (swap : Bool) (left right : CandidateSubstitution n Empty)
    (r p : Recipe 3) (t : Combination (HonestIndex n)) :
    EqE ((frame ns swap left right).eval (mixedCombinationRecipe r p t))
      (.ternary .penc (publicKey ns)
        (.binary .compose ((frame ns swap left right).eval r) (combinationNonce ns t))
        (.binary .add ((frame ns swap left right).eval p) (combinationMessage swap left right t))) :=
  (EqE.binary .mul (.refl _) (combination_value ns swap left right t)).trans
    (RootStep.homomorphic _ _ _ _ _).sound

/-- This nonce decomposition also compares different vote worlds. It does not
assert that the public remainder values themselves agree across those worlds. -/
theorem frame_mixed_nonce_eq_iff (ns : Names n) (hf : ns.Fresh) (swap swap' : Bool)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : r.Public ns.nonceNames) (hs : s.Public ns.nonceNames)
    (a b : Combination (HonestIndex n)) :
    EqE (.binary .compose ((frame ns swap left right).eval r) (combinationNonce ns a))
      (.binary .compose ((frame ns swap' left right).eval s) (combinationNonce ns b)) ↔
      a.indices = b.indices ∧ EqE ((frame ns swap left right).eval r) ((frame ns swap' left right).eval s) :=
  mixed_named_nonce_eq_iff (fun ij : HonestIndex n => ns.nonce ij.1 ij.2) hf.2.1
    (fun ij => ns.nonce_mem_nonceNames ij.1 ij.2) a b _ _
    (frame_recipe_protected_value ns swap left right r hr)
    (frame_recipe_protected_value ns swap' left right s hs)

/-- Exact equality reduction: occurrence bag, public nonce equality and
zero-padded payload equality. Arbitrary public nonce/payload subrecipes remain
inside these smaller observations, rather than being assumed world-independent. -/
theorem mixedCombination_equality_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r p s q : Recipe 3)
    (hr : r.Public ns.nonceNames) (hs : s.Public ns.nonceNames)
    (a b : Combination (HonestIndex n)) :
    EqE ((frame ns swap left right).eval (mixedCombinationRecipe r p a))
      ((frame ns swap left right).eval (mixedCombinationRecipe s q b)) ↔
      a.indices = b.indices ∧
      EqE ((frame ns swap left right).eval r) ((frame ns swap left right).eval s) ∧
      EqE ((frame ns swap left right).eval (.binary .add p (.const .zero)))
        ((frame ns swap left right).eval (.binary .add q (.const .zero))) := by
  have ha := mixedCombination_value ns swap left right r p a
  have hb := mixedCombination_value ns swap left right s q b
  have messages (hi : a.indices = b.indices) :
      EqE (combinationMessage swap left right a) (combinationMessage swap left right b) :=
    (Combination.evaluate_baseEq_of_indices .add trivial
      (fun ij : HonestIndex n => (choice swap left right ij.1).value ij.2) hi).sound
  have numeric := EqE.add_numeric_value_iff_zero
    ((frame ns swap left right).eval p) ((frame ns swap left right).eval q)
    (combinationMessage swap left right a) (combinationMessage_numeric swap left right a)
  constructor
  · intro he
    have hc := (EqE.penc_iff _ _ _ _ _ _).mp (ha.symm.trans (he.trans hb))
    obtain ⟨hi, hn⟩ := (frame_mixed_nonce_eq_iff ns hf swap swap left right r s hr hs a b).mp hc.2.1
    have hp := hc.2.2.trans (EqE.binary .add (.refl _) (messages hi).symm)
    exact ⟨hi, hn, numeric.mp hp⟩
  · rintro ⟨hi, hn, hp⟩
    have hr := (frame_mixed_nonce_eq_iff ns hf swap swap left right r s hr hs a b).mpr ⟨hi, hn⟩
    have hm := (numeric.mpr hp).trans (EqE.binary .add (.refl _) (messages hi))
    exact ha.trans ((EqE.ternary .penc (.refl _) hr hm).trans hb.symm)

/-- This induction step needs only the two smaller equality observations to
transfer. It is not the all-recipe static-equivalence theorem. -/
theorem mixedCombination_equality_swap_of_observations (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (r p s q : Recipe 3)
    (hr : r.Public ns.nonceNames) (hs : s.Public ns.nonceNames)
    (a b : Combination (HonestIndex n))
    (hnonce : EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s))
    (hpayload : EqE ((frame ns false left right).eval (.binary .add p (.const .zero)))
        ((frame ns false left right).eval (.binary .add q (.const .zero))) ↔
      EqE ((frame ns true left right).eval (.binary .add p (.const .zero)))
        ((frame ns true left right).eval (.binary .add q (.const .zero)))) :
    EqE ((frame ns false left right).eval (mixedCombinationRecipe r p a))
      ((frame ns false left right).eval (mixedCombinationRecipe s q b)) ↔
    EqE ((frame ns true left right).eval (mixedCombinationRecipe r p a))
      ((frame ns true left right).eval (mixedCombinationRecipe s q b)) :=
  (mixedCombination_equality_iff ns hf false left right r p s q hr hs a b).trans
    ((and_congr Iff.rfl (and_congr hnonce hpayload)).trans
      (mixedCombination_equality_iff ns hf true left right r p s q hr hs a b).symm)

theorem mixedCombination_subrecipe_bounds (r p : Recipe 3) (t : Combination (HonestIndex n)) :
    r.nodeCount < (mixedCombinationRecipe r p t).nodeCount ∧
      (Term.binary .add p (.const .zero)).nodeCount < (mixedCombinationRecipe r p t).nodeCount := by
  simp only [mixedCombinationRecipe, Term.nodeCount]
  omega

/-- A nonce-public constructor cannot match a value retaining any honest nonce
factor. The public remainder's factor count need not be smaller than the target. -/
theorem mixedCombination_not_public_nonce_constructor (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r p : Recipe 3) (t : Combination (HonestIndex n))
    (key s q : Recipe 3) (hs : s.Public ns.nonceNames) :
    ¬ EqE ((frame ns swap left right).eval (mixedCombinationRecipe r p t))
      ((frame ns swap left right).eval (.ternary .penc key s q)) := by
  intro he
  have hv := mixedCombination_value ns swap left right r p t
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp (hv.symm.trans he)).2.1
  obtain ⟨i, hi⟩ := t.exists_index
  have hfactor : (Term.name (V := Empty) (ns.nonce i.1 i.2)).baseClass ∈
      (Term.binary .compose ((frame ns swap left right).eval r) (combinationNonce ns t)).composeFactors := by
    apply Multiset.mem_add.mpr
    right
    rw [combinationNonce, Combination.named_nonce_factors]
    exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩
  exact frame_nonce_factor_not_deducible ns swap left right s hs
    (ns.nonce_mem_nonceNames i.1 i.2) _ hfactor hn.symm

end ExplainableCrypto.Helios.Symbolic.Historical.General
