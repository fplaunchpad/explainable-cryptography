import ExplainableCrypto.Helios.Computational.BallotProof
import Mathlib.Algebra.BigOperators.Fin

/-! The general finite-component algebra of the neutral-ciphertext attack.
Board freshness and its probability are kept separate from proof validity. -/

namespace ExplainableCrypto.Helios.Computational

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]

structure Ballot (F G : Type) (n : Nat) where
  ciphertext : Fin n → Ciphertext G
  proof : Fin n → Proof01 F G
  overall : Proof01 F G

def Ballot.aggregate {n : Nat} (b : Ballot F G n) : Ciphertext G :=
  ∑ i, b.ciphertext i

def Ballot.Valid {n : Nat} (hash : Hash F G) (g pk : G) (b : Ballot F G n) : Prop :=
  (∀ i, (b.proof i).Valid hash g pk (b.ciphertext i)) ∧
    b.overall.Valid hash g pk b.aggregate

def Ballot.FreshFor {n : Nat} (b : Ballot F G n) (board : List (Ballot F G n)) : Prop :=
  ∀ old ∈ board, ∀ i j, b.ciphertext i ≠ old.ciphertext j

def Ballot.Accepted {n : Nat} (hash : Hash F G) (g pk : G)
    (board : List (Ballot F G n)) (b : Ballot F G n) : Prop :=
  b.Valid hash g pk ∧ b.FreshFor board

def proofReuse {n : Nat} (hash : Hash F G) (g pk : G) (e z w : F)
    (target : Ballot F G (n + 1)) : Ballot F G (n + 1) where
  ciphertext := Fin.cases target.aggregate (fun _ => (0, 0))
  proof := Fin.cases target.overall (fun _ => neutralProof hash g pk e z w)
  overall := target.overall

theorem proofReuse_aggregate {n : Nat} (hash : Hash F G) (g pk : G) (e z w : F)
    (target : Ballot F G (n + 1)) :
    (proofReuse hash g pk e z w target).aggregate = target.aggregate := by
  simp [Ballot.aggregate, proofReuse, Fin.sum_univ_succ]

theorem proofReuse_valid {n : Nat} (hash : Hash F G) (g pk : G) (e z w : F)
    (target : Ballot F G (n + 1)) (ht : target.Valid hash g pk) :
    (proofReuse hash g pk e z w target).Valid hash g pk := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ht.2
    · exact neutralProof_valid hash g pk e z w
  · rw [proofReuse_aggregate]
    exact ht.2

/-- Exact remaining board condition: the attack's aggregate and every neutral
component must avoid earlier ciphertexts. Within-ballot duplicates are allowed. -/
theorem proofReuse_fresh_iff {n : Nat} (hash : Hash F G) (g pk : G) (e z w : F)
    (target : Ballot F G (n + 2)) (board : List (Ballot F G (n + 2))) :
    (proofReuse hash g pk e z w target).FreshFor board ↔
      (∀ old ∈ board, ∀ j, target.aggregate ≠ old.ciphertext j) ∧
      (∀ old ∈ board, ∀ j, (0, 0) ≠ old.ciphertext j) := by
  constructor
  · intro h
    exact ⟨fun old ho j => h old ho 0 j, fun old ho j => h old ho 1 j⟩
  · rintro ⟨ha, hz⟩ old ho i j
    refine Fin.cases (ha old ho j) (fun _ => hz old ho j) i

#print axioms proofReuse_valid
#print axioms proofReuse_fresh_iff

end ExplainableCrypto.Helios.Computational
