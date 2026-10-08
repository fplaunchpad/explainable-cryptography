import ExplainableCrypto.Helios.Computational.BallotProof

/-! BPW section 3: public rerandomization of weak disjunctive proofs.
The ciphertext and responses change, but commitments and challenges do not.
This retained control explains why ciphertext/proof equality checks alone do
not replace the strong Fiat–Shamir part of the selected repair. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

def rerandomizeCiphertext (g pk : G) (delta : F) (ct : Ciphertext G) : Ciphertext G :=
  (ct.1 + delta • g, ct.2 + delta • pk)

def Branch.rerandomize (delta : F) (p : Branch F G) : Branch F G :=
  { p with response := p.response + p.challenge * delta }

def Proof01.rerandomize (delta : F) (p : Proof01 F G) : Proof01 F G :=
  ⟨p.zero.rerandomize delta, p.one.rerandomize delta⟩

theorem Branch.rerandomize_valid (g pk : G) (delta m : F) (ct : Ciphertext G)
    (p : Branch F G) (h : p.Valid g pk ct m) :
    (p.rerandomize delta).Valid g pk (rerandomizeCiphertext g pk delta ct) m := by
  constructor
  · change (p.response + p.challenge * delta) • g =
      p.a + p.challenge • (ct.1 + delta • g)
    rw [add_smul, mul_smul, h.1, smul_add]
    exact add_assoc _ _ _
  · change (p.response + p.challenge * delta) • pk =
      p.b + p.challenge • (ct.2 + delta • pk - m • g)
    have he : ct.2 + delta • pk - m • g = (ct.2 - m • g) + delta • pk := by abel
    rw [add_smul, mul_smul, h.2, he, smul_add]
    exact add_assoc _ _ _

theorem Proof01.rerandomize_valid (hash : Hash F G) (g pk : G) (delta : F)
    (ct : Ciphertext G) (p : Proof01 F G) (h : p.Valid hash g pk ct) :
    (p.rerandomize delta).Valid hash g pk (rerandomizeCiphertext g pk delta ct) :=
  ⟨Branch.rerandomize_valid g pk delta 0 ct p.zero h.1,
    Branch.rerandomize_valid g pk delta 1 ct p.one h.2.1, h.2.2⟩

theorem rerandomizeCiphertext_encryptWith (g pk : G) (delta r m : F) :
    rerandomizeCiphertext g pk delta (encryptWith g pk r m) =
      encryptWith g pk (r + delta) m := by
  ext <;> simp [rerandomizeCiphertext, encryptWith, add_smul, add_assoc]

theorem rerandomizeCiphertext_ne (g pk : G)
    (hg : Function.Injective (fun r : F => r • g)) (delta : F) (hd : delta ≠ 0)
    (ct : Ciphertext G) : rerandomizeCiphertext g pk delta ct ≠ ct := by
  intro he
  have hs : delta • g = (0 : F) • g := by
    have he' := congrArg Prod.fst he
    simpa [rerandomizeCiphertext] using he'
  exact hd (hg hs)

#print axioms Proof01.rerandomize_valid
#print axioms rerandomizeCiphertext_ne

end ExplainableCrypto.Helios.Computational
