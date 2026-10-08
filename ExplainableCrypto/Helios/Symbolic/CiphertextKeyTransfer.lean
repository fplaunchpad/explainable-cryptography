import ExplainableCrypto.Helios.Symbolic.CiphertextObservationInduction
import ExplainableCrypto.Helios.Symbolic.MinimumOriginTools

namespace ExplainableCrypto.Helios.Symbolic.Frame
variable {restricted : Finset Nat} {handles : Nat}

/-- A ciphertext syntax tree retains a strictly smaller public key recipe.
Only comparisons between smaller key recipes cross frames; the ground key
itself may change. Selector witnesses are supplied by the actual frame. -/
theorem ciphertext_syntax_key_transfer (φ ψ : Frame restricted handles)
    (hselected : ∀ v (r : Recipe handles), ProjectionChain v r →
      ∀ key nonce message, EqE (φ.eval r) (.ternary .penc key nonce message) →
      ∃ k : Recipe handles, k.Public restricted ∧ k.nodeCount < r.nodeCount ∧
        EqE (φ.eval k) key ∧ ∃ nonce' message',
          EqE (ψ.eval r) (.ternary .penc (ψ.eval k) nonce' message'))
    (r : Recipe handles) (hs : CiphertextRecipeSyntax r) (hp : r.Public restricted)
    (hobs : ObservationsBelow φ ψ r.nodeCount) {key nonce message : Ground}
    (he : EqE (φ.eval r) (.ternary .penc key nonce message)) :
    ∃ k : Recipe handles, k.Public restricted ∧ k.nodeCount < r.nodeCount ∧
      EqE (φ.eval k) key ∧ ∃ nonce' message',
        EqE (ψ.eval r) (.ternary .penc (ψ.eval k) nonce' message') := by
  induction hs generalizing key nonce message with
  | constructed k s m =>
    refine ⟨k,hp.1,?_,((EqE.penc_iff _ _ _ _ _ _).mp he).1,ψ.eval s,ψ.eval m,.refl _⟩
    simp only [Term.nodeCount]
    omega
  | selected v hc => exact hselected v _ hc _ _ _ he
  | @mul a b ha hb ia ib =>
    obtain ⟨ra,rb,ma,mb,hea,heb,_,_⟩ := he.mul_penc_inversion
    obtain ⟨ka,hka,hsa,hea',na,pa,hva⟩ := ia hp.1
      (hobs.mono (by simp only [Term.nodeCount]; omega)) hea
    obtain ⟨kb,hkb,hsb,heb',nb,pb,hvb⟩ := ib hp.2
      (hobs.mono (by simp only [Term.nodeCount]; omega)) heb
    have hk := (hobs ka kb hka hkb (by simp only [Term.nodeCount]; omega)).mp
      (hea'.trans heb'.symm)
    refine ⟨ka,hka,by simp only [Term.nodeCount]; omega,hea',
      .binary .compose na nb,.binary .add pa pb,?_⟩
    exact (EqE.binary .mul hva (hvb.trans
      (.ternary .penc hk.symm (.refl _) (.refl _)))).trans
      (RootStep.homomorphic _ _ _ _ _).sound

end ExplainableCrypto.Helios.Symbolic.Frame
