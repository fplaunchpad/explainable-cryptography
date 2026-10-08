import ExplainableCrypto.Helios.Symbolic.DecryptCheckTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {restricted : Finset Nat} {n : Nat}

/-- Four smaller public comparisons transfer constructed-proof success. The
encryption-shape comparison costs exactly the proof's size, below the whole
check. All four proof arguments remain bound to the supplied ciphertext. -/
theorem constructed_check_success_transfer (φ ψ : Frame restricted n)
    (a b k r m d : Recipe n) (ha : a.Public restricted) (hb : b.Public restricted)
    (hp : (Term.spk k r m d).Public restricted)
    (hobs : φ.ObservationsBelow ψ (Term.ternary .checkspk a b (.spk k r m d)).nodeCount)
    (he : EqE (φ.eval (.ternary .checkspk a b (.spk k r m d))) (.const .ok)) :
    EqE (ψ.eval (.ternary .checkspk a b (.spk k r m d))) (.const .ok) := by
  obtain ⟨nr,bit,hbit,hcipher,hproof⟩ := (EqE.check_ok_iff_components _ _ _).mp he
  have hs := (EqE.spk_iff _ _ _ _ _ _ _ _).mp hproof
  have hshape : EqE (φ.eval d) (φ.eval (.ternary .penc k r m)) :=
    hs.2.2.2.trans (hcipher.trans (.ternary .penc hs.1.symm hs.2.1.symm hs.2.2.1.symm))
  have hk' := (hobs k a hp.1 ha (by simp only [Term.nodeCount]; omega)).mp hs.1
  have hm' := (hobs m (.const bit) hp.2.2.1 trivial (by simp only [Term.nodeCount]; omega)).mp hs.2.2.1
  have hd' := (hobs d b hp.2.2.2 hb (by simp only [Term.nodeCount]; omega)).mp hs.2.2.2
  have hshape' := (hobs d (.ternary .penc k r m) hp.2.2.2 ⟨hp.1,hp.2.1,hp.2.2.1⟩
    (by simp only [Term.nodeCount]; omega)).mp hshape
  apply (EqE.check_ok_iff_components _ _ _).mpr
  exact ⟨ψ.eval r,bit,hbit,hd'.symm.trans (hshape'.trans (.ternary .penc hk' (.refl _) hm')),
    .spk hk' (.refl _) hm' hd'⟩

end ExplainableCrypto.Helios.Symbolic
