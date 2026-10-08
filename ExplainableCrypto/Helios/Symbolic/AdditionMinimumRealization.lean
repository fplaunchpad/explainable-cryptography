import ExplainableCrypto.Helios.Symbolic.AdditionMinimumCosts

namespace ExplainableCrypto.Helios.Symbolic
variable {V : Type} {restricted : Finset Nat}

/-- A nonempty string of ones, without a redundant leading zero. -/
def positiveOnes : Nat → Term V
  | 0 => .const .one
  | n+1 => .binary .add (positiveOnes n) (.const .one)

def shortAddNumeral : Nat → Term V
  | 0 => .const .zero
  | n+1 => positiveOnes n

theorem positiveOnes_summary (n : Nat) : (positiveOnes (V := V) n).addSyntaxSummary = .number (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [positiveOnes,Term.addSyntaxSummary,ih,AddSummary.combine_numbers]

theorem positiveOnes_public (n : Nat) : (positiveOnes (V := V) n).Public restricted := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,trivial⟩

theorem positiveOnes_nodeCount (n : Nat) : (positiveOnes (V := V) n).nodeCount+1 = 2*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [positiveOnes,Term.nodeCount]; omega

/-- Exact numeric summary and cost, public under any caller policy. -/
theorem shortAddNumeral_properties (n : Nat) :
    (shortAddNumeral (V := V) n).addSyntaxSummary = .number n ∧
    (shortAddNumeral (V := V) n).Public restricted ∧
    (shortAddNumeral (V := V) n).nodeCount+1 = numericRecipeCost (some n) := by
  cases n with
  | zero => exact ⟨rfl,trivial,rfl⟩
  | succ n =>
    refine ⟨positiveOnes_summary n,positiveOnes_public n,?_⟩
    simpa only [shortAddNumeral,numericRecipeCost,max_eq_right (by omega : 1 ≤ n+1)] using
      positiveOnes_nodeCount (V := V) n

/-- Realize a nonempty bag of raw nonnumeric atoms, preserving each occurrence,
publicness and the exact atom cost. -/
theorem realize_add_atoms_minimum_cost (atoms : Multiset (Term V)) (hne : atoms ≠ 0)
    (hshape : ∀ a ∈ atoms, a.addSyntaxSummary = .atom a)
    (hpub : ∀ a ∈ atoms, a.Public restricted) :
    ∃ r : Term V, r.addSyntaxSummary = ⟨atoms,none⟩ ∧ r.Public restricted ∧
      r.nodeCount+1 = (atoms.map (fun a => a.nodeCount+1)).sum := by
  induction atoms using Multiset.induction_on with
  | empty => exact False.elim (hne rfl)
  | cons a atoms ih =>
    have ha := hshape a (by simp)
    have hp := hpub a (by simp)
    by_cases hz : atoms = 0
    · subst atoms
      exact ⟨a,by simpa [AddSummary.atom] using ha,hp,by simp⟩
    · obtain ⟨r,hr,hpr,hcost⟩ := ih hz (fun b hb => hshape b (by simp [hb])) (fun b hb => hpub b (by simp [hb]))
      refine ⟨.binary .add a r,?_,⟨hp,hpr⟩,?_⟩
      · simp only [Term.addSyntaxSummary,ha,hr,AddSummary.combine,AddSummary.atom,numericAdd,Multiset.singleton_add]
      · simp only [Term.nodeCount,Multiset.map_cons,Multiset.sum_cons]
        omega

/-- Every valid nonempty raw skeleton has a public representative attaining
its atom plus normalized numeric cost. -/
theorem realize_add_summary_minimum_cost (s : AddSummary (Term V)) (hne : s ≠ .empty)
    (hshape : ∀ a ∈ s.atoms, a.addSyntaxSummary = .atom a)
    (hpub : ∀ a ∈ s.atoms, a.Public restricted) :
    ∃ r : Term V, r.addSyntaxSummary = s ∧ r.Public restricted ∧ r.nodeCount+1 = s.recipeCost := by
  rcases s with ⟨atoms,num⟩
  cases num with
  | none =>
    have hz : atoms ≠ 0 := fun he => hne (by rw [he]; rfl)
    obtain ⟨r,hr,hp,hc⟩ := realize_add_atoms_minimum_cost atoms hz hshape hpub
    exact ⟨r,hr,hp,by simpa only [AddSummary.recipeCost,numericRecipeCost,Nat.add_zero] using hc⟩
  | some n =>
    have hn := shortAddNumeral_properties (V := V) (restricted := restricted) n
    by_cases hz : atoms = 0
    · subst atoms
      exact ⟨shortAddNumeral n,hn.1,hn.2.1,by simpa only [AddSummary.recipeCost,Multiset.map_zero,Multiset.sum_zero,Nat.zero_add] using hn.2.2⟩
    · obtain ⟨r,hr,hp,hc⟩ := realize_add_atoms_minimum_cost atoms hz hshape hpub
      refine ⟨.binary .add r (shortAddNumeral n),?_,⟨hp,hn.2.1⟩,?_⟩
      · simp only [Term.addSyntaxSummary,hr,hn.1,AddSummary.combine,AddSummary.number,numericAdd,Multiset.add_zero]
      · have hnum := hn.2.2
        simp only [Term.nodeCount,AddSummary.recipeCost]
        omega

/-- Normalize only the outer addition skeleton. Raw E0 equality preserves
all substitutions; every original nonnumeric atom remains an occurrence. -/
theorem public_addition_minimum_cost_representative (r : Term V) (hp : r.Public restricted) :
    ∃ s : Term V, s.Public restricted ∧ BaseEq r s ∧
      s.addSyntaxSummary = r.addSyntaxSummary ∧ s.nodeCount+1 = r.addSyntaxSummary.recipeCost := by
  have info {a : Term V} (ha : a ∈ r.addSyntaxSummary.atoms) :
      a.addSyntaxSummary = .atom a ∧ a.Public restricted := by
    obtain ⟨⟨c,hc⟩,hn,hz,ho⟩ := Term.addSyntaxSummary_mem ha
    exact ⟨Term.addSyntaxSummary_atom hn hz ho,c.public_hole (hc ▸ hp)⟩
  obtain ⟨s,hs,hps,hcost⟩ := realize_add_summary_minimum_cost r.addSyntaxSummary r.addSyntaxSummary_ne_empty
    (fun _ ha => (info ha).1) (fun _ ha => (info ha).2)
  exact ⟨s,hps,baseEq_of_addSyntaxSummary_eq hs.symm,hs,hcost⟩

end ExplainableCrypto.Helios.Symbolic
