import ExplainableCrypto.Helios.Symbolic.NumericHandleCosts

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat}

private theorem numeral_syntax_summary (n : Nat) :
    (addNumeral (V := V) n).addSyntaxSummary = AddSummary.number n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [addNumeral,Term.addSyntaxSummary,ih,AddSummary.combine_numbers]

private theorem numeral_subst (σ : V → Term W) (n : Nat) :
    (addNumeral n).subst σ = addNumeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [addNumeral,Term.subst,ih]

/-- Expanding numeric leaves at the recipe level realizes the exact raw E0
summary, even if an unexpanded nonnumeric leaf can itself reduce. -/
theorem Term.addNumericValue_syntax_summary (ν : V → Option Nat) (r : Term V) :
    (r.addNumericValue Term.var ν).addSyntaxSummary = r.addNumericSummary ν := by
  induction r with
  | binary f a b ia ib =>
    cases f <;> simp only [addNumericValue,subst_var,addSyntaxSummary,addNumericSummary,ia,ib]
  | const c => cases c <;> rfl
  | var v =>
    cases hv : ν v <;> simp only [addNumericValue,addNumericSummary,hv,addSyntaxSummary,numeral_syntax_summary]
  | _ => simp only [addNumericValue,subst_var,addSyntaxSummary,addNumericSummary]

/-- Numeric expansion commutes with substitution because literal numerals
contain no handles. -/
theorem Term.addNumericValue_subst (σ : V → Term W) (ν : V → Option Nat) (r : Term V) :
    (r.addNumericValue Term.var ν).subst σ = r.addNumericValue σ ν := by
  induction r with
  | binary f a b ia ib =>
    cases f <;> simp only [addNumericValue,subst_var,Term.subst,ia,ib]
  | const c => cases c <;> rfl
  | var v => cases hv : ν v <;> simp only [addNumericValue,hv,Term.subst,numeral_subst]
  | _ => simp only [addNumericValue,subst_var]

/-- Equal handle-aware syntax summaries imply equality in every substitution
satisfying the numeric-handle table. Semantic atom conditions are unnecessary
for this sound direction. -/
theorem eqE_of_addNumericSummary_eq (σ : V → Term W) (ν : V → Option Nat)
    (hn : ∀ v n, ν v = some n → EqE (σ v) (addNumeral n)) {r s : Term V}
    (hs : r.addNumericSummary ν = s.addNumericSummary ν) : EqE (r.subst σ) (s.subst σ) := by
  have hbase := baseEq_of_addSyntaxSummary_eq
    ((r.addNumericValue_syntax_summary ν).trans (hs.trans (s.addNumericValue_syntax_summary ν).symm))
  have he := hbase.sound.subst σ
  rw [Term.addNumericValue_subst,Term.addNumericValue_subst] at he
  exact (r.addNumericValue_eq σ ν hn).trans (he.trans (s.addNumericValue_eq σ ν hn).symm)

/-- Numeric-aware summaries never lose the last contribution. -/
theorem Term.addNumericSummary_ne_empty (ν : V → Option Nat) (r : Term V) :
    r.addNumericSummary ν ≠ AddSummary.empty := by
  rw [← r.addNumericValue_syntax_summary ν]
  exact Term.addSyntaxSummary_ne_empty _

/-- A raw nonnumeric leaf that is not marked numeric has singleton summary. -/
theorem Term.addNumericSummary_atom (ν : V → Option Nat) {r : Term V}
    (ha : ∀ a b, r ≠ .binary .add a b) (hz : r ≠ .const .zero) (ho : r ≠ .const .one)
    (hv : ∀ v, r = .var v → ν v = none) : r.addNumericSummary ν = AddSummary.atom r := by
  cases r with
  | binary f a b => cases f <;> first | rfl | exact False.elim (ha a b rfl)
  | const c => cases c <;> first | rfl | exact False.elim (hz rfl) | exact False.elim (ho rfl)
  | var v => simp only [addNumericSummary,hv v rfl]
  | _ => rfl

/-- Realize every nonnumeric atom occurrence at its original syntax cost. -/
theorem realize_numeric_handle_atoms (ν : V → Option Nat) (atoms : Multiset (Term V)) (hne : atoms ≠ 0)
    (hshape : ∀ a ∈ atoms, a.addNumericSummary ν = AddSummary.atom a)
    (hpub : ∀ a ∈ atoms, a.Public restricted) :
    ∃ r : Term V, r.addNumericSummary ν = ⟨atoms,none⟩ ∧ r.Public restricted ∧
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
      · simp only [Term.addNumericSummary,ha,hr,AddSummary.combine,AddSummary.atom,numericAdd,Multiset.singleton_add]
      · simp only [Term.nodeCount,Multiset.map_cons,Multiset.sum_cons]
        omega

/-- An arbitrary nonempty valid summary attains its atom-plus-numeric cost.
The numeric expression may reuse published handles as many times as needed. -/
theorem realize_numeric_handle_summary (ν : V → Option Nat) (s : AddSummary (Term V)) (hne : s ≠ .empty)
    (hshape : ∀ a ∈ s.atoms, a.addNumericSummary ν = AddSummary.atom a)
    (hpub : ∀ a ∈ s.atoms, a.Public restricted) :
    ∃ r : Term V, r.addNumericSummary ν = s ∧ r.Public restricted ∧
      r.nodeCount+1 = s.numericHandleRecipeCost ν := by
  rcases s with ⟨atoms,num⟩
  cases num with
  | none =>
    have hz : atoms ≠ 0 := fun he => hne (by rw [he]; rfl)
    obtain ⟨r,hr,hp,hc⟩ := realize_numeric_handle_atoms ν atoms hz hshape hpub
    exact ⟨r,hr,hp,by simpa only [AddSummary.numericHandleRecipeCost,numericHandleCost,Nat.add_zero] using hc⟩
  | some n =>
    obtain ⟨t,ht,hn,hcost⟩ := numericHandleCost_realized ν n
    by_cases hz : atoms = 0
    · subst atoms
      exact ⟨t,hn,ht.public restricted,by simpa only [AddSummary.numericHandleRecipeCost,Multiset.map_zero,Multiset.sum_zero,Nat.zero_add] using hcost⟩
    · obtain ⟨r,hr,hp,hc⟩ := realize_numeric_handle_atoms ν atoms hz hshape hpub
      refine ⟨.binary .add r t,?_,⟨hp,ht.public restricted⟩,?_⟩
      · simp only [Term.addNumericSummary,hr,hn,AddSummary.combine,AddSummary.number,numericAdd,Multiset.add_zero]
      · simp only [Term.nodeCount,AddSummary.numericHandleRecipeCost]
        omega

/-- Any public outer addition skeleton has a summary-preserving representative
attaining the exact numeric-handle cost; original atom occurrences are retained. -/
theorem public_numeric_handle_cost_representative (ν : V → Option Nat) (r : Term V)
    (hp : r.Public restricted) :
    ∃ s : Term V, s.Public restricted ∧ s.addNumericSummary ν = r.addNumericSummary ν ∧
      s.nodeCount+1 = (r.addNumericSummary ν).numericHandleRecipeCost ν := by
  have info {a : Term V} (ha : a ∈ (r.addNumericSummary ν).atoms) :
      a.addNumericSummary ν = AddSummary.atom a ∧ a.Public restricted := by
    obtain ⟨⟨c,hc⟩,hn,hz,ho,hv⟩ := Term.addNumericSummary_mem ν ha
    exact ⟨Term.addNumericSummary_atom ν hn hz ho hv,c.public_hole (hc ▸ hp)⟩
  obtain ⟨s,hs,hps,hcost⟩ := realize_numeric_handle_summary ν (r.addNumericSummary ν) (r.addNumericSummary_ne_empty ν)
    (fun _ ha => (info ha).1) (fun _ ha => (info ha).2)
  exact ⟨s,hps,hs,hcost⟩

end ExplainableCrypto.Helios.Symbolic
