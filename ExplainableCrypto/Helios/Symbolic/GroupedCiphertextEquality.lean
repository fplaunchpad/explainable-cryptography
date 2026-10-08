import ExplainableCrypto.Helios.Symbolic.CiphertextGroupingSoundness

namespace ExplainableCrypto.Helios.Symbolic
variable {V α : Type} {restricted : Finset Nat}

/-- A protected remainder has at least one non-honest outer factor. It cannot
vanish into an all-honest nonce bag; no injectivity or unit premise is used. -/
theorem mixed_nonce_not_honest (names : α → Nat) (hnames : ∀ i, names i ∈ restricted)
    (a b : Combination α) (r : Term V) (hr : ProtectedValue restricted r) :
    ¬ EqE (.binary .compose r (a.evaluate .compose (fun i => .name (names i))))
      (b.evaluate .compose (fun i => .name (names i))) := by
  intro he
  obtain ⟨r', her, hnr, hsr⟩ := hr.normal_rep
  have he' := (EqE.binary .compose her (.refl _)).symm.trans he
  have hb := (irreducible_eqE_iff_base (hnr.compose (Combination.named_nonce_irreducible names a))
    (Combination.named_nonce_irreducible names b)).mp he'
  obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero r'.composeFactors_nonempty
  have hmem : q ∈ (Term.binary .compose r' (a.evaluate .compose (fun i => .name (names i)))).composeFactors :=
    Multiset.mem_add.mpr (Or.inl hq)
  rw [hb.compose_factors, Combination.named_nonce_factors] at hmem
  obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hmem
  exact r'.nonce_safe_no_name_factor hsr (hnames i) (hi ▸ hq)

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

private theorem public_nonce_not_honest (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r : Recipe 3) (hr : r.Public ns.nonceNames)
    (a : Combination (HonestIndex n)) :
    ¬ EqE ((frame ns swap left right).eval r) (combinationNonce ns a) := by
  obtain ⟨i, hi⟩ := a.exists_index
  apply frame_nonce_factor_not_deducible ns swap left right r hr (ns.nonce_mem_nonceNames i.1 i.2)
  rw [combinationNonce, Combination.named_nonce_factors]
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

private theorem public_nonce_not_mixed (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3) (hr : r.Public ns.nonceNames)
    (a : Combination (HonestIndex n)) :
    ¬ EqE ((frame ns swap left right).eval r)
      (.binary .compose ((frame ns swap left right).eval s) (combinationNonce ns a)) := by
  obtain ⟨i, hi⟩ := a.exists_index
  apply frame_nonce_factor_not_deducible ns swap left right r hr (ns.nonce_mem_nonceNames i.1 i.2)
  apply Multiset.mem_add.mpr
  right
  rw [combinationNonce, Combination.named_nonce_factors]
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

namespace CiphertextGroup

/-- Exact public observations for equal grouped components. Cross-case equality
is false; numeric padding applies only when an honest part is present. -/
def Observation (φ : Frame restricted handles) : CiphertextGroup n handles → CiphertextGroup n handles → Prop
  | .constructed r p, .constructed s q => EqE (φ.eval r) (φ.eval s) ∧ EqE (φ.eval p) (φ.eval q)
  | .honest a, .honest b => a.indices = b.indices
  | .mixed r p a, .mixed s q b => a.indices = b.indices ∧ EqE (φ.eval r) (φ.eval s) ∧
      EqE (φ.eval (.binary .add p (.const .zero))) (φ.eval (.binary .add q (.const .zero)))
  | _, _ => False

/-- All nine group comparisons are classified. Publicness is needed for the
nonce remainders; payload publicness is retained for later observation transfer. -/
theorem components_eq_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextGroup n)
    (ha : a.Public ns.nonceNames) (hb : b.Public ns.nonceNames) :
    (EqE (a.nonce ns (frame ns swap left right)) (b.nonce ns (frame ns swap left right)) ∧
      EqE (a.message (frame ns swap left right) swap left right)
        (b.message (frame ns swap left right) swap left right)) ↔
    Observation (frame ns swap left right) a b := by
  cases a with
  | constructed r p =>
    cases b with
    | constructed s q => exact Iff.rfl
    | honest b => exact iff_false_intro (fun h => public_nonce_not_honest ns swap left right r ha.1 b h.1)
    | mixed s q b => exact iff_false_intro (fun h => public_nonce_not_mixed ns swap left right r s ha.1 b h.1)
  | honest a =>
    cases b with
    | constructed s q => exact iff_false_intro (fun h => public_nonce_not_honest ns swap left right s hb.1 a h.1.symm)
    | honest b =>
      constructor
      · intro h
        exact (Combination.named_nonce_eq_iff _ hf.2.1 a b).mp h.1
      · intro hi
        exact ⟨(Combination.named_nonce_eq_iff _ hf.2.1 a b).mpr hi,
          (Combination.evaluate_baseEq_of_indices .add trivial _ hi).sound⟩
    | mixed s q b =>
      exact iff_false_intro (fun h => mixed_nonce_not_honest _
        (fun i : HonestIndex n => ns.nonce_mem_nonceNames i.1 i.2) b a _
        (frame_recipe_protected_value ns swap left right s hb.1) h.1.symm)
  | mixed r p a =>
    cases b with
    | constructed s q => exact iff_false_intro (fun h => public_nonce_not_mixed ns swap left right s r hb.1 a h.1.symm)
    | honest b =>
      exact iff_false_intro (fun h => mixed_nonce_not_honest _
        (fun i : HonestIndex n => ns.nonce_mem_nonceNames i.1 i.2) a b _
        (frame_recipe_protected_value ns swap left right r ha.1) h.1)
    | mixed s q b =>
      have hv₁ := mixedCombination_value ns swap left right r p a
      have hv₂ := mixedCombination_value ns swap left right s q b
      have heq := mixedCombination_equality_iff ns hf swap left right r p s q ha.1 hb.1 a b
      constructor
      · intro h
        exact heq.mp (hv₁.trans ((EqE.ternary .penc (.refl _) h.1 h.2).trans hv₂.symm))
      · intro h
        exact ((EqE.penc_iff _ _ _ _ _ _).mp (hv₁.symm.trans ((heq.mpr h).trans hv₂))).2

/-- Arbitrary semantic keys remain an explicit public equality observation. -/
theorem ciphertext_eq_iff (ns : Names n) (hf : ns.Fresh) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (a b : CiphertextGroup n)
    (ha : a.Public ns.nonceNames) (hb : b.Public ns.nonceNames) (k l : Ground) :
    EqE (.ternary .penc k (a.nonce ns (frame ns swap left right))
        (a.message (frame ns swap left right) swap left right))
      (.ternary .penc l (b.nonce ns (frame ns swap left right))
        (b.message (frame ns swap left right) swap left right)) ↔
    EqE k l ∧ Observation (frame ns swap left right) a b :=
  (EqE.penc_iff _ _ _ _ _ _).trans
    (and_congr Iff.rfl (components_eq_iff ns hf swap left right a b ha hb))

end CiphertextGroup
end ExplainableCrypto.Helios.Symbolic.Historical.General
