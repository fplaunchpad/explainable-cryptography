import ExplainableCrypto.Helios.Symbolic.SourceVoterNonceScopes

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {n : Nat}

/-- A concrete allocation above a supplied bound, with disjoint intervals
for the two honest voters' nonces. No candidate term is rewritten. -/
def allocateElectionNames (n bound : Nat) : Names n :=
  ⟨bound,bound+1,fun i j => bound+2+i.val*(n+1)+j.val⟩

theorem allocateElectionNames_fresh (n bound : Nat) : (allocateElectionNames n bound).Fresh := by
  refine ⟨by simp [allocateElectionNames],?_,?_⟩
  · intro a b h
    obtain ⟨i,j⟩ := a
    obtain ⟨k,l⟩ := b
    have hi : i=k := by
      apply Fin.ext
      fin_cases i <;> fin_cases k
      all_goals simp only [allocateElectionNames,Nat.zero_mul,Nat.one_mul] at h ⊢
      all_goals omega
    subst k
    congr 1
    apply Fin.ext
    change bound+2+i.val*(n+1)+j.val = bound+2+i.val*(n+1)+l.val at h
    omega
  · intro i j
    dsimp [allocateElectionNames]
    omega

theorem allocateElectionNames_above (n bound : Nat) (m : Nat)
    (hm : m ∈ (allocateElectionNames n bound).restricted) : bound ≤ m := by
  simp only [Names.restricted,Names.nonceNames,Finset.mem_union,Finset.mem_insert,
    Finset.mem_singleton,Finset.mem_image,Finset.mem_univ,true_and] at hm
  rcases hm with (rfl | rfl) | ⟨ij,rfl⟩
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _
  · dsimp [allocateElectionNames]
    omega

/-- Allocate all private base names outside an arbitrary finite set. -/
theorem exists_fresh_election_names (n : Nat) (avoid : Finset Nat) :
    ∃ ns : Names n, ns.Fresh ∧ ∀ m ∈ ns.restricted, m ∉ avoid := by
  let bound := avoid.sup id + 1
  refine ⟨allocateElectionNames n bound,allocateElectionNames_fresh n bound,?_⟩
  intro m hm ha
  have hlo := allocateElectionNames_above n bound m hm
  have hhi : m ≤ avoid.sup id := Finset.le_sup (f := id) ha
  dsimp [bound] at hlo
  omega

/-- Every full candidate term contributes its literal names, including names
inside fields that E could later discard. -/
def candidateParameterNames (left right : Fin (n+1) → Ground) : Finset Nat :=
  Finset.univ.biUnion (fun j => (left j).nameSupport ∪ (right j).nameSupport)

theorem noncesFreshFor_of_avoids (ns : Names n) (left right : Fin (n+1) → Ground)
    (hf : ∀ m ∈ ns.restricted, m ∉ candidateParameterNames left right) :
    NoncesFreshFor ns left ∧ NoncesFreshFor ns right := by
  have hnonce (i : Fin 2) (j : Fin (n+1)) : ns.nonce i j ∈ ns.restricted := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
  constructor <;> intro i j k hk
  all_goals apply hf _ (hnonce i j)
  · exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,Finset.mem_union_left _ hk⟩
  · exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_univ _,Finset.mem_union_right _ hk⟩

/-- The nonce-freshness premise of the scope theorem is satisfiable for every
pair of full ground parameter vectors, while leaving both vectors unchanged. -/
theorem exists_parameter_fresh_election (left right : Fin (n+1) → Ground) :
    ∃ ns : Names n, ns.Fresh ∧ NoncesFreshFor ns left ∧ NoncesFreshFor ns right ∧
      (∀ m ∈ ns.restricted, m ∉ candidateParameterNames left right) := by
  obtain ⟨ns,hn,hf⟩ := exists_fresh_election_names n (candidateParameterNames left right)
  obtain ⟨hl,hr⟩ := noncesFreshFor_of_avoids ns left right hf
  exact ⟨ns,hn,hl,hr,hf⟩

/-- A single allocation supports the literal interleaved voter scopes in both
swapped worlds, for every honest voter channel. -/
theorem exists_scoped_voter_allocation (left right : CandidateSubstitution n Empty) :
    ∃ ns : Names n, ns.Fresh ∧ ∀ swap i channel,
      Named.Structural ((scopedVoterProgram ns i (choice swap left right i).value).compile channel)
        (Named.restrictNames (voterNonceList ns i)
          (.embed (.plain (.output channel (ballot ns i (choice swap left right i).value) .nil)))) := by
  obtain ⟨ns,hn,hl,hr,_⟩ := exists_parameter_fresh_election left.value right.value
  refine ⟨ns,hn,?_⟩
  intro swap i channel
  apply scopedVoterProgram_normalizes ns hn i _ _ channel
  unfold choice
  split <;> cases swap <;> assumption

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
