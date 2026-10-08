import ExplainableCrypto.Helios.Symbolic.NumericHandleRealization
import ExplainableCrypto.Helios.Symbolic.PaddedPayloadMinima

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type} {restricted : Finset Nat}

/-- Padding supplies zero presence while preserving every nonnumeric atom
and the numeric total of the handle-aware outer addition skeleton. -/
theorem Term.padded_addNumericSummary (ν : V → Option Nat) (r : Term V) :
    (Term.binary .add r (.const .zero)).addNumericSummary ν =
      ⟨(r.addNumericSummary ν).atoms,some ((r.addNumericSummary ν).numeric.getD 0)⟩ := by
  simp only [addNumericSummary,AddSummary.number,AddSummary.combine,Multiset.add_zero,numericAdd_zero]

/-- Least padded skeleton cost. A zero total needs no numeric contribution
when atoms remain, but the complete recipe always has at least one node.
Positive totals use available numeric handles rather than literal-only costs. -/
noncomputable def AddSummary.paddedNumericHandleRecipeCost (ν : V → Option Nat) (s : AddSummary (Term V)) : Nat :=
  max 2 ((s.atoms.map (fun a => a.nodeCount+1)).sum +
    if s.numeric.getD 0 = 0 then 0 else numericHandleCost ν (some (s.numeric.getD 0)))

/-- Every public or private raw recipe pays at least its padded skeleton cost. -/
theorem Term.paddedNumericHandleRecipeCost_le (ν : V → Option Nat) (r : Term V) :
    (r.addNumericSummary ν).paddedNumericHandleRecipeCost ν ≤ r.nodeCount+1 := by
  have h := r.addNumericSummary_cost_le ν
  have hp := r.nodeCount_pos
  have hn : (if (r.addNumericSummary ν).numeric.getD 0 = 0 then 0
      else numericHandleCost ν (some ((r.addNumericSummary ν).numeric.getD 0))) ≤
      numericHandleCost ν (r.addNumericSummary ν).numeric := by
    cases (r.addNumericSummary ν).numeric with
    | none => simp
    | some n => simp only [Option.getD]; split <;> omega
  simp only [AddSummary.paddedNumericHandleRecipeCost,AddSummary.numericHandleRecipeCost] at *
  omega

/-- Equal padded syntax summaries preserve values for every substitution
satisfying the same numeric-handle table. No semantic atom premise is needed. -/
theorem padded_eqE_of_addNumericSummary (σ : V → Term W) (ν : V → Option Nat)
    (hn : ∀ v n, ν v = some n → EqE (σ v) (addNumeral n)) {r s : Term V}
    (ha : (r.addNumericSummary ν).atoms=(s.addNumericSummary ν).atoms)
    (ht : (r.addNumericSummary ν).numeric.getD 0=(s.addNumericSummary ν).numeric.getD 0) :
    EqE ((Term.binary .add r (.const .zero)).subst σ) ((Term.binary .add s (.const .zero)).subst σ) := by
  apply eqE_of_addNumericSummary_eq σ ν hn
  simp only [Term.padded_addNumericSummary,ha,ht]

private theorem pure_padded_cost (ν : V → Option Nat) (n : Nat) :
    max 2 (if n=0 then 0 else numericHandleCost ν (some n)) = numericHandleCost ν (some n) := by
  by_cases hz : n=0
  · simp [hz,(numericHandleCost_bits ν).1]
  · simp only [hz,↓reduceIte]
    exact max_eq_right (numericHandleCost_ge_two ν n)

/-- Every public skeleton attains its padded cost, retaining its exact atom
bag and numeric total. The representative is portable across all substitutions
satisfying the table; zero-only payloads never become empty terms. -/
theorem public_padded_numeric_handle_cost_representative (ν : V → Option Nat) (r : Term V)
    (hp : r.Public restricted) :
    ∃ s : Term V, s.Public restricted ∧
      (s.addNumericSummary ν).atoms=(r.addNumericSummary ν).atoms ∧
      (s.addNumericSummary ν).numeric.getD 0=(r.addNumericSummary ν).numeric.getD 0 ∧
      s.nodeCount+1=(r.addNumericSummary ν).paddedNumericHandleRecipeCost ν := by
  classical
  let n := (r.addNumericSummary ν).numeric.getD 0
  have info {a : Term V} (ha : a ∈ (r.addNumericSummary ν).atoms) :
      a.addNumericSummary ν=AddSummary.atom a ∧ a.Public restricted := by
    obtain ⟨⟨c,hc⟩,hn,hz,ho,hv⟩ := Term.addNumericSummary_mem ν ha
    exact ⟨Term.addNumericSummary_atom ν hn hz ho hv,c.public_hole (hc ▸ hp)⟩
  by_cases hz : (r.addNumericSummary ν).atoms=0
  · obtain ⟨s,hs,he,hc⟩ := numericHandleCost_realized ν n
    refine ⟨s,hs.public restricted,by simp only [he,AddSummary.number,hz],by simp only [he,AddSummary.number,Option.getD]; rfl,?_⟩
    simpa only [AddSummary.paddedNumericHandleRecipeCost,hz,Multiset.map_zero,Multiset.sum_zero,Nat.zero_add,
      pure_padded_cost] using hc
  · by_cases hn : n=0
    · obtain ⟨s,hs,hps,hc⟩ := realize_numeric_handle_atoms ν (r.addNumericSummary ν).atoms hz
        (fun _ ha => (info ha).1) (fun _ ha => (info ha).2)
      have hpos := s.nodeCount_pos
      refine ⟨s,hps,by rw [hs],?_,?_⟩
      · change (s.addNumericSummary ν).numeric.getD 0=n
        simp only [hs,Option.getD,hn]
      · simp only [AddSummary.paddedNumericHandleRecipeCost]
        change s.nodeCount+1=max 2 ((Multiset.map (fun a => a.nodeCount+1) (r.addNumericSummary ν).atoms).sum + if n=0 then 0 else numericHandleCost ν (some n))
        simp only [hn,↓reduceIte,Nat.add_zero]
        omega
    · obtain ⟨s,hs,hps,hc⟩ := realize_numeric_handle_summary ν ⟨(r.addNumericSummary ν).atoms,some n⟩
        (by intro h; have he := congrArg AddSummary.numeric h; cases he) (fun _ ha => (info ha).1) (fun _ ha => (info ha).2)
      have hpos := s.nodeCount_pos
      refine ⟨s,hps,by rw [hs],by simp only [hs,Option.getD]; rfl,?_⟩
      simp only [AddSummary.numericHandleRecipeCost] at hc
      simp only [AddSummary.paddedNumericHandleRecipeCost]
      change s.nodeCount+1=max 2 ((Multiset.map (fun a => a.nodeCount+1) (r.addNumericSummary ν).atoms).sum + if n=0 then 0 else numericHandleCost ν (some n))
      simp only [hn,↓reduceIte]
      omega

end ExplainableCrypto.Helios.Symbolic
