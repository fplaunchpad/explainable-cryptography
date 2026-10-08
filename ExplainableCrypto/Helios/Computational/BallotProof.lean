import Examples.ElGamal.Basic

/-! Smyth's disjunctive ballot-proof algorithms, in additive group notation.
`0 : G` represents the multiplicative group identity. The hash input contains
only the four commitments, as in section 2.2 of the May 2012 manuscript.
These equations are separate from the protocol's probabilistic sampling policy.
-/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

abbrev Ciphertext (G : Type) := G × G

def encryptWith (g pk : G) (r m : F) : Ciphertext G :=
  (r • g, m • g + r • pk)

/-- The deterministic body is exactly the selected library's ElGamal
encryption; the historical nonzero sampling policy is handled separately. -/
theorem encryptWith_vcvio [Fintype F] [DecidableEq F] [SampleableType F]
    [SampleableType G] (g pk : G) (m : F) :
    (elGamalAsymmEnc F G g).encrypt pk (m • g) =
      (do
        let r ← uniformSample F
        pure (encryptWith g pk r m)) := rfl

structure Branch (F G : Type) where
  a : G
  b : G
  challenge : F
  response : F

structure Proof01 (F G : Type) where
  zero : Branch F G
  one : Branch F G

abbrev Hash (F G : Type) := (G × G) × (G × G) → F

def Branch.Valid (g pk : G) (ct : Ciphertext G) (m : F) (p : Branch F G) : Prop :=
  p.response • g = p.a + p.challenge • ct.1 ∧
  p.response • pk = p.b + p.challenge • (ct.2 - m • g)

def Proof01.Valid (hash : Hash F G) (g pk : G) (ct : Ciphertext G)
    (p : Proof01 F G) : Prop :=
  p.zero.Valid g pk ct 0 ∧ p.one.Valid g pk ct 1 ∧
    p.zero.challenge + p.one.challenge = hash ((p.zero.a, p.zero.b), (p.one.a, p.one.b))

def realBranch (g pk : G) (r w e : F) : Branch F G :=
  ⟨w • g, w • pk, e, w + r * e⟩

def simulatedBranch (g pk : G) (ct : Ciphertext G) (m e z : F) : Branch F G :=
  ⟨z • g - e • ct.1, z • pk - e • (ct.2 - m • g), e, z⟩

theorem realBranch_valid (g pk : G) (m r w e : F) :
    (realBranch g pk r w e).Valid g pk (encryptWith g pk r m) m := by
  simp [Branch.Valid, realBranch, encryptWith, add_smul,
    smul_smul, mul_comm, add_sub_cancel_left]

theorem simulatedBranch_valid (g pk : G) (ct : Ciphertext G) (m e z : F) :
    (simulatedBranch g pk ct m e z).Valid g pk ct m := by
  simp [Branch.Valid, simulatedBranch]

def proveZero (hash : Hash F G) (g pk : G) (r w e z : F) : Proof01 F G :=
  let one := simulatedBranch g pk (encryptWith g pk r 0) 1 e z
  let challenge := hash ((w • g, w • pk), (one.a, one.b)) - e
  ⟨realBranch g pk r w challenge, one⟩

def proveOne (hash : Hash F G) (g pk : G) (r w e z : F) : Proof01 F G :=
  let zero := simulatedBranch g pk (encryptWith g pk r 1) 0 e z
  let challenge := hash ((zero.a, zero.b), (w • g, w • pk)) - e
  ⟨zero, realBranch g pk r w challenge⟩

theorem proveZero_valid (hash : Hash F G) (g pk : G) (r w e z : F) :
    (proveZero hash g pk r w e z).Valid hash g pk (encryptWith g pk r 0) := by
  refine ⟨realBranch_valid _ _ _ _ _ _, simulatedBranch_valid _ _ _ _ _ _, ?_⟩
  simp [proveZero, realBranch, simulatedBranch]

theorem proveOne_valid (hash : Hash F G) (g pk : G) (r w e z : F) :
    (proveOne hash g pk r w e z).Valid hash g pk (encryptWith g pk r 1) := by
  refine ⟨simulatedBranch_valid _ _ _ _ _ _, realBranch_valid _ _ _ _ _ _, ?_⟩
  simp [proveOne, realBranch, simulatedBranch]

/-- Smyth section 3.1: a valid proof for the neutral ciphertext, constructed
without a secret key and for every hash function. Honest encryption's nonzero
nonce policy imposes no restriction on adversarial proof construction. -/
def neutralProof (hash : Hash F G) (g pk : G) (e z w : F) : Proof01 F G :=
  ⟨⟨w • g, w • pk, hash ((w • g, w • pk), (z • g, z • pk + e • g)) - e, w⟩,
    ⟨z • g, z • pk + e • g, e, z⟩⟩

theorem neutralProof_valid (hash : Hash F G) (g pk : G) (e z w : F) :
    (neutralProof hash g pk e z w).Valid hash g pk (0, 0) := by
  simp [Proof01.Valid, Branch.Valid, neutralProof]

#print axioms proveZero_valid
#print axioms proveOne_valid
#print axioms neutralProof_valid

end ExplainableCrypto.Helios.Computational
