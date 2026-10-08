import ExplainableCrypto.Helios.Computational.PrimeSimCommitCallerOrigins

namespace ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
open OracleComp OracleSpec BitOracleMachine
set_option maxHeartbeats 300000
set_option maxRecDepth 65536
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
-- Keep proof-side unification from executing the concrete arithmetic clock.
-- Execution is rewritten only through the checked run theorems below.
attribute [local irreducible] BitOracleMachine.run

/-- Extract the actual typed predecessor and charge bound from the completed
raw prefix's checked query-tree law. No reconstruction premise is supplied. -/
private theorem prefix_support {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (first : PrimeHonestTranscriptCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeHonestTranscriptCaller.code
      (PrimeHonestTranscriptCaller.clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (PrimeHonestTranscriptCaller.start (PrimeHonestInputMachine.input g pk slack vote saved)))) :
    ∃ out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q),
      first.1 = PrimeHonestTranscriptCaller.sourceResult slack g pk vote saved out ∧
      first.2 ≤ PrimeHonestTranscriptCaller.cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q := by
  have hm : first.1 ∈ support (Prod.fst <$> BitOracleMachine.run PrimeHonestTranscriptCaller.code
      (PrimeHonestTranscriptCaller.clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (PrimeHonestTranscriptCaller.start (PrimeHonestInputMachine.input g pk slack vote saved))) := by
    rw [support_map]
    exact ⟨first,hf,rfl⟩
  rw [PrimeHonestTranscriptCaller.execution_source,simulateQ_map] at hm
  obtain ⟨out,_,ho⟩ := mem_support_map_peel _ _ hm
  exact ⟨out,ho,(PrimeHonestTranscriptCaller.run_support slack g pk vote saved first hf).2⟩

private theorem supported_return {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (first : PrimeHonestTranscriptCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeHonestTranscriptCaller.code
      (PrimeHonestTranscriptCaller.clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (PrimeHonestTranscriptCaller.start (PrimeHonestInputMachine.input g pk slack vote saved)))) :
    BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
      (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])) =
    BitOracleReturnLink.embed commitLabel none (PrimeSimCommitMachine.start first.1.stk) := by
  obtain ⟨out,he,_⟩ := prefix_support slack g pk vote saved first hf
  rw [he]
  exact prefix_return _

private theorem tail_bound {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool)
    (first : PrimeHonestTranscriptCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeHonestTranscriptCaller.code
      (PrimeHonestTranscriptCaller.clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (PrimeHonestTranscriptCaller.start (PrimeHonestInputMachine.input g pk slack vote saved)))) :
    ∀ last ∈ support (BitOracleMachine.run PrimeSimCommitMachine.code (PrimeSimCommitMachine.clock p q)
      (PrimeSimCommitMachine.start first.1.stk)),
      last.1.l = none ∧ last.2 ≤ PrimeSimCommitMachine.cost p q := by
  obtain ⟨out,he,_⟩ := prefix_support slack g pk vote saved first hf
  obtain ⟨c,hc,hr⟩ := PrimeSimCommitMachine.charged_source slack g pk vote saved out
  rw [he,hr]
  intro last hl
  have he := eq_of_mem_support_pure _ hl
  subst last
  exact ⟨rfl,hc⟩

/-- One actual raw execution frames the existing prefix and returns live to
the first commitment controller, preserving both query trees and actual charges. -/
theorem linked_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    let raw := PrimeHonestInputMachine.input g pk slack vote saved
    BitOracleMachine.run code (clock raw slack p q) (start raw) = (do
      let first ← BitOracleMachine.run PrimeHonestTranscriptCaller.code
        (PrimeHonestTranscriptCaller.clock raw slack p q) (PrimeHonestTranscriptCaller.start raw)
      let last ← BitOracleMachine.run PrimeSimCommitMachine.code (PrimeSimCommitMachine.clock p q)
        (PrimeSimCommitMachine.start first.1.stk)
      pure (BitOracleReturnLink.embed commitLabel none last.1,first.2+last.2)) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote saved
  have hframe := BitOracleStackFrame.run prefixLayout PrimeHonestTranscriptCaller.code
    (PrimeHonestTranscriptCaller.clock raw slack p q) (PrimeHonestTranscriptCaller.start raw) (fun _ => [])
  change BitOracleMachine.run prefixCode (PrimeHonestTranscriptCaller.clock raw slack p q)
    (BitOracleStackFrame.embed prefixLayout (PrimeHonestTranscriptCaller.start raw) (fun _ => [])) = _ at hframe
  have hh : ∀ out ∈ support (BitOracleMachine.run prefixCode
      (PrimeHonestTranscriptCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeHonestTranscriptCaller.start raw) (fun _ => []))), out.1.l = none := by
    rw [hframe]
    intro out ho
    obtain ⟨first,hf,rfl⟩ := mem_support_map_peel _ _ ho
    exact (PrimeHonestTranscriptCaller.run_support slack g pk vote saved first hf).1
  have ht : ∀ out ∈ support (BitOracleMachine.run prefixCode
      (PrimeHonestTranscriptCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeHonestTranscriptCaller.start raw) (fun _ => []))),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q)
        (BitOracleReturnLink.embed prefixLabel (some (commitLabel 0)) out.1)), last.1.l = none := by
    rw [hframe]
    intro out ho
    obtain ⟨first,hf,he⟩ := mem_support_map_peel _ _ ho
    subst out
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSimCommitMachine.clock p q)
      (BitOracleReturnLink.embed prefixLabel (some (commitLabel 0))
        (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])))), last.1.l = none
    rw [supported_return slack g pk vote saved first hf,
      BitOracleReturnLink.rename_run _ _ _ commit_code]
    intro last hl
    obtain ⟨sourceOut,hs,_⟩ := prefix_support slack g pk vote saved first hf
    obtain ⟨charge,_,hr⟩ := PrimeSimCommitMachine.charged_source slack g pk vote saved sourceOut
    rw [hs,hr,map_pure] at hl
    have he := eq_of_mem_support_pure _ hl
    rw [he]
    rfl
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code _ _ _ hh ht,hframe]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  apply bind_congr_of_forall_mem_support
  intro first hf
  rw [supported_return slack g pk vote saved first hf,
    BitOracleReturnLink.rename_run _ _ _ commit_code]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- The full raw caller's leaf cost is the derived sum of actual prefix and
commitment costs. All final workspace and source-state conditions are reached. -/
theorem run_support {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    ∀ out ∈ support (BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote saved))),
      out.1.l = none ∧ out.2 ≤ cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q := by
  rw [linked_run]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨first,hf,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨last,hl,ho⟩ := ho
  have he := eq_of_mem_support_pure _ ho
  subst out
  have hp := PrimeHonestTranscriptCaller.run_support slack g pk vote saved first hf
  have ht := tail_bound slack g pk vote saved first hf last hl
  constructor
  · change last.1.l.elim none (some ∘ commitLabel) = none
    rw [ht.1]
    rfl
  · change first.2+last.2 ≤ _
    exact Nat.add_le_add hp.2 ht.2

private theorem within_support (limit bound : Nat) (oa : OracleComp spec (Config × Nat))
    (h : ∀ out ∈ support oa, out.1.l = none ∧ out.2 ≤ bound) :
    BitOracleLoopBounded.Within limit bound oa := by
  induction oa using OracleComp.inductionOn with
  | pure out => exact h out (by simp)
  | query_bind t next ih =>
    intro answer _
    apply ih answer
    intro out ho
    exact h out (by
      rw [mem_support_bind_iff]
      exact ⟨answer,by simp only [support_liftM]; exact ⟨answer,rfl⟩,ho⟩)

theorem within {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack limit : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (saved : List Bool) :
    BitOracleLoopBounded.Within limit
      (cost (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
      (BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote saved) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote saved))) := by
  exact within_support limit _ _ (run_support slack g pk vote saved)

#print axioms linked_run
#print axioms run_support
#print axioms within
end ExplainableCrypto.Helios.Computational.PrimeSimCommitCaller
