import ExplainableCrypto.Helios.Symbolic.DecryptCheckSingleMixedTransport

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat}

/-- Padding supplies numeric presence but contributes no ones. -/
theorem numericAdd_zero (o : Option Nat) : numericAdd o (some 0) = some (o.getD 0) := by
  cases o <;> simp [numericAdd]

theorem Term.padded_addSyntaxSummary (r : Term V) :
    (Term.binary .add r (.const .zero)).addSyntaxSummary =
      ⟨r.addSyntaxSummary.atoms,some (r.addSyntaxSummary.numeric.getD 0)⟩ := by
  simp only [addSyntaxSummary,AddSummary.number,AddSummary.combine,Multiset.add_zero,numericAdd_zero]

/-- Minimum raw payload cost under padded equality. All-zero payloads still
need a real one-node zero recipe; no empty object-language term is introduced. -/
def AddSummary.paddedRecipeCost (s : AddSummary (Term V)) : Nat :=
  max 2 ((s.atoms.map (fun a => a.nodeCount+1)).sum + 2*s.numeric.getD 0)

theorem Term.paddedRecipeCost_le (r : Term V) : r.addSyntaxSummary.paddedRecipeCost ≤ r.nodeCount+1 := by
  have h := r.addSyntaxSummary_cost_le
  have hp := r.nodeCount_pos
  have hn : 2*r.addSyntaxSummary.numeric.getD 0 ≤ numericRecipeCost r.addSyntaxSummary.numeric := by
    cases r.addSyntaxSummary.numeric <;> simp only [Option.getD,numericRecipeCost] <;> omega
  simp only [AddSummary.paddedRecipeCost,AddSummary.recipeCost] at *
  omega

theorem padded_baseEq_of_atoms_numeric {r s : Term V}
    (ha : r.addSyntaxSummary.atoms=s.addSyntaxSummary.atoms)
    (hn : r.addSyntaxSummary.numeric.getD 0=s.addSyntaxSummary.numeric.getD 0) :
    BaseEq (.binary .add r (.const .zero)) (.binary .add s (.const .zero)) := by
  apply baseEq_of_addSyntaxSummary_eq
  simp only [Term.padded_addSyntaxSummary,ha,hn]

/-- Remove redundant numeric zeros from the outer skeleton while retaining
every atom and one. Equality is asserted after padding, not before padding. -/
theorem public_padded_minimum_cost_representative (r : Term V) (hp : r.Public restricted) :
    ∃ s : Term V, s.Public restricted ∧
      BaseEq (.binary .add r (.const .zero)) (.binary .add s (.const .zero)) ∧
      s.addSyntaxSummary.atoms=r.addSyntaxSummary.atoms ∧
      s.nodeCount+1=r.addSyntaxSummary.paddedRecipeCost := by
  let n := r.addSyntaxSummary.numeric.getD 0
  have hn := shortAddNumeral_properties (V := V) (restricted := restricted) n
  have info {a : Term V} (ha : a ∈ r.addSyntaxSummary.atoms) :
      a.addSyntaxSummary = .atom a ∧ a.Public restricted := by
    obtain ⟨⟨c,hc⟩,hna,hz,ho⟩ := Term.addSyntaxSummary_mem ha
    exact ⟨Term.addSyntaxSummary_atom hna hz ho,c.public_hole (hc ▸ hp)⟩
  by_cases hz : r.addSyntaxSummary.atoms=0
  · have he := padded_baseEq_of_atoms_numeric (r := r) (s := shortAddNumeral n)
      (by simp only [hn.1,AddSummary.number,hz]) (by simp only [hn.1,AddSummary.number,Option.getD]; rfl)
    refine ⟨shortAddNumeral n,hn.2.1,he,by simp only [hn.1,AddSummary.number,hz],?_⟩
    rw [hn.2.2]
    simp only [AddSummary.paddedRecipeCost,hz,Multiset.map_zero,Multiset.sum_zero,Nat.zero_add,numericRecipeCost]
    change 2*max 1 n=max 2 (2*n)
    omega
  · obtain ⟨a,ha,hpa,hca⟩ := realize_add_atoms_minimum_cost r.addSyntaxSummary.atoms hz
      (fun _ h => (info h).1) (fun _ h => (info h).2)
    have hpos := a.nodeCount_pos
    by_cases hzero : n=0
    · refine ⟨a,hpa,padded_baseEq_of_atoms_numeric (by rw [ha]) ?_,by rw [ha],?_⟩
      · change n = a.addSyntaxSummary.numeric.getD 0
        simp only [ha,Option.getD,hzero]
      · simp only [AddSummary.paddedRecipeCost]
        change a.nodeCount+1=max 2 ((r.addSyntaxSummary.atoms.map (fun a => a.nodeCount+1)).sum+2*n)
        omega
    · let s : Term V := .binary .add a (shortAddNumeral n)
      have hs : s.addSyntaxSummary=⟨r.addSyntaxSummary.atoms,some n⟩ := by
        simp only [s,Term.addSyntaxSummary,ha,hn.1,AddSummary.combine,AddSummary.number,Multiset.add_zero,numericAdd]
      refine ⟨s,⟨hpa,hn.2.1⟩,padded_baseEq_of_atoms_numeric (by rw [hs]) ?_,by rw [hs],?_⟩
      · simp only [hs,Option.getD]; rfl
      · have hcn := hn.2.2
        simp only [s,Term.nodeCount,AddSummary.paddedRecipeCost,numericRecipeCost] at *
        change 1+a.nodeCount+(shortAddNumeral (V := V) n).nodeCount+1 =
          max 2 ((r.addSyntaxSummary.atoms.map (fun a => a.nodeCount+1)).sum+2*n)
        omega

end ExplainableCrypto.Helios.Symbolic
