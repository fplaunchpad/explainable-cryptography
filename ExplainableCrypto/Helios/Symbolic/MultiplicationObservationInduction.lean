import ExplainableCrypto.Helios.Symbolic.MultiplicationPartitionTransfer

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- The complete non-ciphertext multiplication branch groups all ciphertext
fusions, derives strictly smaller public group recipes in both worlds, and
reassembles their transferred equality. Destination minimum size is not assumed. -/
theorem minimum_non_ciphertext_multiplication_equality_swap (ns : Names n)
    (left right : CandidateSubstitution n Empty) (r s : Recipe 3)
    (hr : MinimalRecipe ns.restricted (frame ns false left right).value r)
    (hs : MinimalRecipe ns.restricted (frame ns false left right).value s)
    {x y u v : Ground}
    (her : EqE ((frame ns false left right).eval r) (.binary .mul x y))
    (hes : EqE ((frame ns false left right).eval s) (.binary .mul u v))
    (hnr : ¬ ((frame ns false left right).eval r).CiphertextValue)
    (hns : ¬ ((frame ns false left right).eval s).CiphertextValue)
    (hobs : (frame ns false left right).ObservationsBelow (frame ns true left right)
      (r.nodeCount + s.nodeCount)) :
    EqE ((frame ns false left right).eval r) ((frame ns false left right).eval s) ↔
      EqE ((frame ns true left right).eval r) ((frame ns true left right).eval s) := by
  obtain ⟨a, b, rfl⟩ := minimum_non_ciphertext_mul_form ns false left right ns.restricted r hr her hnr
  obtain ⟨c, d, rfl⟩ := minimum_non_ciphertext_mul_form ns false left right ns.restricted s hs hes hns
  obtain ⟨⟨af, bf, hf, p, hp⟩, ⟨adest, bdest, ht, p', hp'⟩⟩ :=
    minimum_non_ciphertext_mul_partitions ns left right a b hr hnr (hobs.mono (by omega))
  obtain ⟨⟨cf, df, hg, q, hq⟩, ⟨ct, dt, hu, q', hq'⟩⟩ :=
    minimum_non_ciphertext_mul_partitions ns left right c d hs hns (hobs.mono (by omega))
  constructor
  · intro he
    apply p.transfer_normal_equality q hf hg (frame ns true left right).value ?_ he
    intro x hx y hy hxy
    have hpx := hp x hx
    have hqy := hq y hy
    exact (hobs x.1 y.1 hpx.1 hqy.1 (by omega)).mp hxy
  · intro he
    apply p'.transfer_normal_equality q' ht hu (frame ns false left right).value ?_ he
    intro x hx y hy hxy
    have hpx := hp' x hx
    have hqy := hq' y hy
    exact (hobs x.1 y.1 hpx.1 hqy.1 (by omega)).mpr hxy

end ExplainableCrypto.Helios.Symbolic.Historical.General
