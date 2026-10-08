import ExplainableCrypto.Helios.Symbolic.MixedNonceProvenance
import ExplainableCrypto.Helios.Symbolic.OpaqueComposedNames

namespace ExplainableCrypto.Helios.Symbolic
variable {V α : Type} {restricted : Finset Nat}

/-- Opaque protection survives normalization while allowing restricted names
inside cryptographic data that public recipes cannot expose. -/
theorem OpaqueProtectedValue.normal_rep {r : Term V} (h : OpaqueProtectedValue restricted r) :
    ∃ r', EqE r r' ∧ Irreducible r' ∧ r'.opaqueSafe restricted = true := by
  obtain ⟨r₀,he,hs⟩ := h
  obtain ⟨r',hp,hn⟩ := exists_normal_form r₀
  exact ⟨r',he.trans hp.sound,hn,hp.to_modulo.opaque_safe hs⟩

/-- Opaque public remainders cannot compensate for a changed honest nonce bag.
The existing normal-factor separation proof retains all repeated occurrences. -/
theorem opaque_mixed_named_nonce_eq_iff (names : α → Nat) (hf : Function.Injective names)
    (hnames : ∀ i, names i ∈ restricted) (a b : Combination α) (r s : Term V)
    (hr : OpaqueProtectedValue restricted r) (hs : OpaqueProtectedValue restricted s) :
    EqE (.binary .compose r (a.evaluate .compose (fun i => .name (names i))))
      (.binary .compose s (b.evaluate .compose (fun i => .name (names i)))) ↔
      a.indices = b.indices ∧ EqE r s := by
  apply mixed_named_nonce_eq_iff_of_normal_factors names hf a b r s
  · obtain ⟨r',he,hn,hs⟩ := hr.normal_rep
    exact ⟨r',he,hn,fun i => r'.opaque_safe_no_name_factor hs (hnames i)⟩
  · obtain ⟨s',he,hn,hs⟩ := hs.normal_rep
    exact ⟨s',he,hn,fun i => s'.opaque_safe_no_name_factor hs (hnames i)⟩

/-- An opaque public remainder contains at least one non-honest factor. It
cannot disappear into an all-honest nonce bag, even when it reduces internally. -/
theorem opaque_mixed_nonce_not_honest (names : α → Nat) (hnames : ∀ i, names i ∈ restricted)
    (a b : Combination α) (r : Term V) (hr : OpaqueProtectedValue restricted r) :
    ¬ EqE (.binary .compose r (a.evaluate .compose (fun i => .name (names i))))
      (b.evaluate .compose (fun i => .name (names i))) := by
  intro he
  obtain ⟨r',her,hnr,hsr⟩ := hr.normal_rep
  have he' := (EqE.binary .compose her (.refl _)).symm.trans he
  have hb := (irreducible_eqE_iff_base (hnr.compose (Combination.named_nonce_irreducible names a))
    (Combination.named_nonce_irreducible names b)).mp he'
  obtain ⟨q,hq⟩ := Multiset.exists_mem_of_ne_zero r'.composeFactors_nonempty
  have hmem : q ∈ (Term.binary .compose r' (a.evaluate .compose (fun i => .name (names i)))).composeFactors :=
    Multiset.mem_add.mpr (Or.inl hq)
  rw [hb.compose_factors,Combination.named_nonce_factors] at hmem
  obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp hmem
  exact r'.opaque_safe_no_name_factor hsr (hnames i) (hi ▸ hq)

end ExplainableCrypto.Helios.Symbolic
