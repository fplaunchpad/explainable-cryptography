import ExplainableCrypto.Helios.Symbolic.GroupedCiphertextEquality
import ExplainableCrypto.Helios.Symbolic.OpaqueMixedNonces
import ExplainableCrypto.Helios.Symbolic.CiphertextObservationInduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n handles : Nat} {restricted : Finset Nat}

private theorem opaque_public_nonce_not_honest (ns : Names n) (φ : Frame restricted handles)
    (hφ : φ.OpaqueProtected) (hnames : ∀ i : HonestIndex n, ns.nonce i.1 i.2 ∈ restricted)
    (r : Recipe handles) (hr : r.Public restricted) (a : Combination (HonestIndex n)) :
    ¬ EqE (φ.eval r) (combinationNonce ns a) := by
  obtain ⟨i,hi⟩ := a.exists_index
  apply hφ.name_factor_not_deducible r hr (hnames i)
  rw [combinationNonce,Combination.named_nonce_factors]
  exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩

private theorem opaque_public_nonce_not_mixed (ns : Names n) (φ : Frame restricted handles)
    (hφ : φ.OpaqueProtected) (hnames : ∀ i : HonestIndex n, ns.nonce i.1 i.2 ∈ restricted)
    (r s : Recipe handles) (hr : r.Public restricted) (a : Combination (HonestIndex n)) :
    ¬ EqE (φ.eval r) (.binary .compose (φ.eval s) (combinationNonce ns a)) := by
  obtain ⟨i,hi⟩ := a.exists_index
  apply hφ.name_factor_not_deducible r hr (hnames i)
  apply Multiset.mem_add.mpr
  right
  rw [combinationNonce,Combination.named_nonce_factors]
  exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩

namespace CiphertextGroup

/-- Exact nine-case component classification for any opaque-protected frame
whose public-name policy protects the honest nonces. Numeric padding appears
only when an honest contribution is present. -/
theorem components_eq_iff_of_opaque_protected (ns : Names n) (hf : ns.Fresh)
    (φ : Frame restricted handles) (hφ : φ.OpaqueProtected)
    (hnames : ∀ i : HonestIndex n, ns.nonce i.1 i.2 ∈ restricted)
    (swap : Bool) (left right : CandidateSubstitution n Empty) (a b : CiphertextGroup n handles)
    (ha : a.Public restricted) (hb : b.Public restricted) :
    (EqE (a.nonce ns φ) (b.nonce ns φ) ∧
      EqE (a.message φ swap left right) (b.message φ swap left right)) ↔ Observation φ a b := by
  cases a with
  | constructed r p =>
    cases b with
    | constructed s q => exact Iff.rfl
    | honest b => exact iff_false_intro (fun h => opaque_public_nonce_not_honest ns φ hφ hnames r ha.1 b h.1)
    | mixed s q b => exact iff_false_intro (fun h => opaque_public_nonce_not_mixed ns φ hφ hnames r s ha.1 b h.1)
  | honest a =>
    cases b with
    | constructed s q => exact iff_false_intro (fun h => opaque_public_nonce_not_honest ns φ hφ hnames s hb.1 a h.1.symm)
    | honest b =>
      constructor
      · intro h
        exact (Combination.named_nonce_eq_iff _ hf.2.1 a b).mp h.1
      · intro hi
        exact ⟨(Combination.named_nonce_eq_iff _ hf.2.1 a b).mpr hi,
          (Combination.evaluate_baseEq_of_indices .add trivial _ hi).sound⟩
    | mixed s q b =>
      exact iff_false_intro (fun h => opaque_mixed_nonce_not_honest _ hnames b a _ (hφ.eval s hb.1) h.1.symm)
  | mixed r p a =>
    cases b with
    | constructed s q => exact iff_false_intro (fun h => opaque_public_nonce_not_mixed ns φ hφ hnames s r hb.1 a h.1.symm)
    | honest b =>
      exact iff_false_intro (fun h => opaque_mixed_nonce_not_honest _ hnames a b _ (hφ.eval r ha.1) h.1)
    | mixed s q b =>
      have hn := opaque_mixed_named_nonce_eq_iff (fun i : HonestIndex n => ns.nonce i.1 i.2)
        hf.2.1 hnames a b (φ.eval r) (φ.eval s) (hφ.eval r ha.1) (hφ.eval s hb.1)
      have messages (hi : a.indices = b.indices) :
          EqE (combinationMessage swap left right a) (combinationMessage swap left right b) :=
        (Combination.evaluate_baseEq_of_indices .add trivial _ hi).sound
      have padded := EqE.add_numeric_value_iff_zero (φ.eval p) (φ.eval q)
        (combinationMessage swap left right a) (combinationMessage_numeric swap left right a)
      constructor
      · intro he
        obtain ⟨hi,hr⟩ := hn.mp he.1
        exact ⟨hi,hr,padded.mp (he.2.trans (EqE.binary .add (.refl _) (messages hi).symm))⟩
      · rintro ⟨hi,hr,hp⟩
        exact ⟨hn.mpr ⟨hi,hr⟩,(padded.mpr hp).trans (EqE.binary .add (.refl _) (messages hi))⟩

/-- Semantic ciphertext keys remain a separate explicit equality observation. -/
theorem ciphertext_eq_iff_of_opaque_protected (ns : Names n) (hf : ns.Fresh)
    (φ : Frame restricted handles) (hφ : φ.OpaqueProtected)
    (hnames : ∀ i : HonestIndex n, ns.nonce i.1 i.2 ∈ restricted)
    (swap : Bool) (left right : CandidateSubstitution n Empty) (a b : CiphertextGroup n handles)
    (ha : a.Public restricted) (hb : b.Public restricted) (k l : Ground) :
    EqE (.ternary .penc k (a.nonce ns φ) (a.message φ swap left right))
      (.ternary .penc l (b.nonce ns φ) (b.message φ swap left right)) ↔
      EqE k l ∧ Observation φ a b :=
  (EqE.penc_iff _ _ _ _ _ _).trans
    (and_congr Iff.rfl (components_eq_iff_of_opaque_protected ns hf φ hφ hnames swap left right a b ha hb))

/-- Group costs leave strict room for each public nonce/payload comparison,
including zero padding. No group observation or static equivalence is assumed. -/
theorem observation_transfer_of_group_bounds (φ ψ : Frame restricted handles)
    (a b : CiphertextGroup n handles) (ha : a.Public restricted) (hb : b.Public restricted)
    (hobs : φ.ObservationsBelow ψ (a.budget+b.budget)) : Observation φ a b ↔ Observation ψ a b := by
  exact CiphertextGroup.observation_transfer φ ψ a b ha hb (Nat.le_refl _) (Nat.le_refl _) hobs

end CiphertextGroup
end ExplainableCrypto.Helios.Symbolic.Historical.General
