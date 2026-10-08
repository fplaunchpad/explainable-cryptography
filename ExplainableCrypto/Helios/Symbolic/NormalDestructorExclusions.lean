import ExplainableCrypto.Helios.Symbolic.MultiplicationObservationInduction

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type}

/-- A normal projection cannot have any pair E-value as its argument. -/
theorem Irreducible.projection_no_pair {f : Unary} (hf : f = .fst ∨ f = .snd)
    {a : Term V} (ht : Irreducible (.unary f a)) :
    ∀ x y, ¬ EqE a (.binary .pair x y) := by
  intro x y he
  have ha := ht.context_hole (.unary f .hole)
  obtain ⟨u, v, rfl, _⟩ := he.symm.passive_binary_irreducible_shape (Or.inl rfl) ha
  rcases hf with rfl | rfl
  · exact ht u (RootStep.fst u v).to_modulo
  · exact ht v (RootStep.snd u v).to_modulo

/-- Reachable E5/E6 argument matching would provide a modulo step out of the
normal whole term, even when the original arguments are not literal redexes. -/
theorem Irreducible.decryption_no_match {a b : Term V}
    (ht : Irreducible (.binary .dec a b)) : ∀ m, ¬ DecryptionMatch a b m := by
  rintro m ⟨k, r, hk, hc⟩
  rcases hk with hk | hk
  · have hb := ht.reducesModulo (ReducesModulo.binary .dec hk hc)
    exact ht m ((RootStep.decrypt k r m).to_modulo.pre_base hb)
  · have hb := ht.reducesModulo (ReducesModulo.binary .dec hk hc)
    exact ht m ((RootStep.partial_decrypt k r m).to_modulo.pre_base hb)

/-- A normal proof check cannot have a reachable successful match. -/
theorem Irreducible.proof_check_no_match {a b c : Term V}
    (ht : Irreducible (.ternary .checkspk a b c)) : ¬ ProofCheckMatch a b c := by
  intro hm
  have hh := (ht.reducesModulo hm.reduces).head_eq
  cases hh

end ExplainableCrypto.Helios.Symbolic
