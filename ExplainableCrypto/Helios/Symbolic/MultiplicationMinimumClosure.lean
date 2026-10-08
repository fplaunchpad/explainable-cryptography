import ExplainableCrypto.Helios.Symbolic.MultiplicationMinimumPartitions

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat} {σ : V → Term W}

/-- One source recipe may represent a whole fused ciphertext group. Only its
target must be a single multiplication factor; the source syntax is arbitrary. -/
def MultiplicationPartition.single (r : Term V) (a : Term W)
    (hp : r.Public restricted) (he : EqE (r.subst σ) a)
    (hf : a.mulFactors = {a.baseClass}) : MultiplicationPartition restricted σ r a where
  pieces := {(r,a)}
  sourceFactors := by simp
  targetFactors := by simpa using hf.symm
  values := by intro x hx; have h := Multiset.mem_singleton.mp hx; subst x; exact he
  publicPieces := by intro x hx; have h := Multiset.mem_singleton.mp hx; subst x; exact hp
  budget := by simp
  value := he

end ExplainableCrypto.Helios.Symbolic

namespace ExplainableCrypto.Helios.Symbolic.Historical.General
variable {n : Nat}

/-- Two minimum groups remain minimum as a product when their selected
single-factor representatives form a fully normal endpoint. This includes
ciphertext groups and excludes further fusion via the explicit normality premise. -/
theorem minimum_mul_of_normal_groups (ns : Names n) (swap : Bool)
    (left right : CandidateSubstitution n Empty) (restricted : Finset Nat) (a b : Recipe 3)
    (ha : MinimalRecipe restricted (frame ns swap left right).value a)
    (hb : MinimalRecipe restricted (frame ns swap left right).value b)
    {u v : Ground} (hea : EqE ((frame ns swap left right).eval a) u)
    (heb : EqE ((frame ns swap left right).eval b) v)
    (hu : u.mulFactors = {u.baseClass}) (hv : v.mulFactors = {v.baseClass})
    (hn : Irreducible (.binary .mul u v)) :
    MinimalRecipe restricted (frame ns swap left right).value (.binary .mul a b) := by
  let p := (MultiplicationPartition.single a u ha.isPublic hea hu).mul
    (MultiplicationPartition.single b v hb.isPublic heb hv)
  apply minimum_of_normal_partition ns swap left right restricted (.binary .mul a b)
    ⟨ha.isPublic,hb.isPublic⟩ p hn
  intro x hx
  simp only [p,MultiplicationPartition.mul,MultiplicationPartition.single,
    Multiset.mem_add,Multiset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ha
  · exact hb

end ExplainableCrypto.Helios.Symbolic.Historical.General
