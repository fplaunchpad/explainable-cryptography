import ExplainableCrypto.Helios.Symbolic.SourceFreshElectionAllocation
import ExplainableCrypto.Helios.Symbolic.SourceUnusedRestrictions

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V : Type} {n : Nat}

theorem foldCandidates_public (op : Binary) (values : Fin (n+1) → Term V) (restricted : Finset Nat)
    (hp : ∀ j, (values j).Public restricted) : (foldCandidates op values).Public restricted := by
  have fold (xs : List (Fin n)) (acc : Term V) (ha : acc.Public restricted) :
      (xs.foldl (fun a j => .binary op a (values j.succ)) acc).Public restricted := by
    induction xs generalizing acc with
    | nil => exact ha
    | cons j js ih => exact ih _ ⟨ha,hp _⟩
  exact fold _ _ (hp 0)

/-- Full ballot syntax is public under any policy that permits its key,
nonce and parameter terms. All four proof fields are retained. -/
theorem ballot_public_of_parameters (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground)
    (restricted : Finset Nat) (hk : (publicKey ns).Public restricted)
    (hn : ∀ j, ns.nonce i j ∉ restricted) (hv : ∀ j, (values j).Public restricted) :
    (ballot ns i values).Public restricted := by
  have hc (j) : (General.ciphertext ns i values j).Public restricted := ⟨hk,hn j,hv j⟩
  have hp (j) : (General.componentProof ns i values j).Public restricted := ⟨hk,hn j,hv j,hc j⟩
  have ha : (General.aggregateProof ns i values).Public restricted :=
    ⟨hk,foldCandidates_public .compose _ restricted hn,
      foldCandidates_public .add _ restricted hv,foldCandidates_public .mul _ restricted hc⟩
  apply Term.Public.tuple
  intro t ht
  simp only [General.ballotFields,List.mem_append,List.mem_map,List.mem_singleton] at ht
  rcases ht with (⟨j,_,rfl⟩ | ⟨j,_,rfl⟩) | rfl
  · exact hc _
  · exact hp _
  · exact ha

/-- One honest voter's full ballot contains no nonce from the other voter,
provided the full candidate terms avoid the allocated nonce families. -/
theorem ballot_other_nonce_fresh (ns : Names n) (hf : ns.Fresh) (i k : Fin 2) (hik : i ≠ k)
    (j : Fin (n+1)) (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) :
    ns.nonce k j ∉ (ballot ns i values).nameSupport := by
  have hp : (ballot ns i values).Public {ns.nonce k j} := by
    apply ballot_public_of_parameters ns i values _
    · simpa only [publicKey,Term.Public,Finset.mem_singleton] using (hf.2.2 k j).1.symm
    · intro l h
      have he : (i,l) = (k,j) := hf.2.1 (Finset.mem_singleton.mp h)
      exact hik (congrArg Prod.fst he)
    · intro l
      apply (Term.public_iff_nameSupport _ _).mpr
      intro u hu hm
      exact hv k j l ((Finset.mem_singleton.mp hm) ▸ hu)
  intro hm
  exact (Term.public_iff_nameSupport _ _).mp hp _ hm (Finset.mem_singleton_self _)

def voterOutput (ns : Names n) (i : Fin 2) (values : Fin (n+1) → Ground) (channel : Nat) : Named Empty :=
  .embed (.plain (.output channel (ballot ns i values) .nil))

theorem voterOutput_other_nonce_fresh (ns : Names n) (hf : ns.Fresh) (i k : Fin 2) (hik : i ≠ k)
    (values : Fin (n+1) → Ground) (hv : NoncesFreshFor ns values) (channel : Nat)
    (u : SourceName) (hu : u ∈ voterNonceList ns k) : u ∉ (voterOutput ns i values channel).freeNames := by
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hu
  simpa [voterOutput,Named.freeNames,Extended.nameSupport,Agent.nameSupport] using
    ballot_other_nonce_fresh ns hf i k hik j values hv

/-- Both source voter blocks, with their interleaved scopes, beside a supplied
administration context. Its free-name condition is explicit in the theorem. -/
def scopedVotersWith (ns : Names n) (left right : Fin (n+1) → Ground)
    (c₀ c₁ : Nat) (context : Named Empty) : Named Empty :=
  .par ((scopedVoterProgram ns 0 left).compile c₀)
    (.par ((scopedVoterProgram ns 1 right).compile c₁) context)

theorem scopedVotersWith_normalizes (ns : Names n) (hf : ns.Fresh)
    (left right : Fin (n+1) → Ground) (hl : NoncesFreshFor ns left) (hr : NoncesFreshFor ns right)
    (c₀ c₁ : Nat) (context : Named Empty)
    (hc : ∀ u ∈ voterNonceList ns 0 ++ voterNonceList ns 1, u ∉ context.freeNames) :
    Named.Structural (scopedVotersWith ns left right c₀ c₁ context)
      (Named.restrictNames (voterNonceList ns 0 ++ voterNonceList ns 1)
        (.par (voterOutput ns 0 left c₀) (.par (voterOutput ns 1 right c₁) context))) := by
  let a := voterOutput ns 0 left c₀
  let b := voterOutput ns 1 right c₁
  let as := voterNonceList ns 0
  let bs := voterNonceList ns 1
  have h₀ := scopedVoterProgram_normalizes ns hf 0 left hl c₀
  have h₁ := scopedVoterProgram_normalizes ns hf 1 right hr c₁
  have hab : ∀ u ∈ as, u ∉ b.freeNames :=
    voterOutput_other_nonce_fresh ns hf 1 0 (by decide) right hr c₁
  have hba : ∀ u ∈ bs, u ∉ a.freeNames :=
    voterOutput_other_nonce_fresh ns hf 0 1 (by decide) left hl c₀
  have hac : ∀ u ∈ as, u ∉ context.freeNames := fun u hu => hc u (List.mem_append_left _ hu)
  have hbc : ∀ u ∈ bs, u ∉ context.freeNames := fun u hu => hc u (List.mem_append_right _ hu)
  have habc : ∀ u ∈ as, u ∉ (Named.par b context).freeNames := by
    intro u hu
    exact fun h => (Finset.mem_union.mp h).elim (hab u hu) (hac u hu)
  have haprefix : ∀ u ∈ as, u ∉ (Named.restrictNames bs (.par b context)).freeNames := by
    intro u hu hm
    exact habc u hu ((by rw [Named.freeNames_restrictNames] at hm; exact (Finset.mem_sdiff.mp hm).1))
  apply (Named.Structural.parLeft _ h₀).trans
  apply (Named.Structural.parRight _ (Named.Structural.parLeft _ h₁)).trans
  apply (Named.Structural.parRight _ (Named.Structural.par_restrictNames_left b context bs hbc)).trans
  apply (Named.Structural.par_restrictNames_left a _ as haprefix).trans
  have h := (Named.Structural.par_restrictNames_right a (.par b context) bs hba).restrictNames as
  simpa only [Named.restrictNames_append] using h

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
