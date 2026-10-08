import ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
import ExplainableCrypto.Helios.Computational.PrimeSecondKeyMachineSource

namespace ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
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
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (first : PrimeSecondAllCommitCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeSecondAllCommitCaller.code
      (PrimeSecondAllCommitCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeSecondAllCommitCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    ∃ out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q),
      ∃ cs : ZMod q × ZMod q × ZMod q × ZMod q,
      first.1 = PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs ∧
      first.2 ≤ PrimeSecondAllCommitCaller.cost (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q := by
  have hm : first.1 ∈ support (Prod.fst <$> BitOracleMachine.run PrimeSecondAllCommitCaller.code
      (PrimeSecondAllCommitCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeSecondAllCommitCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)))) := by
    rw [support_map]
    exact ⟨first,hf,rfl⟩
  rw [PrimeSecondAllCommitCaller.execution_source] at hm
  obtain ⟨out,cs,ho⟩ := PrimeSecondAllCommitCaller.source_support slack g pk vote s live first.1 hm
  exact ⟨out,cs,ho,(PrimeSecondAllCommitCaller.run_support slack g pk vote s live first hf).2⟩

private theorem supported_return {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (first : PrimeSecondAllCommitCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeSecondAllCommitCaller.code
      (PrimeSecondAllCommitCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeSecondAllCommitCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])) =
    BitOracleReturnLink.embed tailLabel none (PrimeSecondKeyMachine.start first.1.stk) := by
  obtain ⟨out,cs,he,_⟩ := prefix_support slack g pk vote s live first hf
  rw [he]
  exact prefix_return _

private theorem tail_bound {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (first : PrimeSecondAllCommitCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeSecondAllCommitCaller.code
      (PrimeSecondAllCommitCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeSecondAllCommitCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    ∀ last ∈ support (BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
      (PrimeSecondKeyMachine.start first.1.stk)),
      last.1.l = none ∧ last.2 ≤ PrimeSecondKeyMachine.cost p := by
  obtain ⟨out,cs,he,_⟩ := prefix_support slack g pk vote s live first hf
  obtain ⟨charge,hc,hr⟩ := PrimeSecondKeyMachine.charged_source slack g pk vote s live out cs
  change BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
    (PrimeSecondKeyMachine.start (PrimeSecondAllCommitCaller.sourceResult slack g pk vote s live out cs).stk) = _ at hr
  rw [he,hr]
  intro last hl
  have heq := eq_of_mem_support_pure _ hl
  subst last
  exact ⟨rfl,hc⟩

/-- One actual raw execution frames the existing prefix and returns live to
the original p1 key serialization, preserving both query trees and actual charges. -/
theorem linked_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    BitOracleMachine.run code (clock raw slack p q) (start raw) = (do
      let first ← BitOracleMachine.run PrimeSecondAllCommitCaller.code
        (PrimeSecondAllCommitCaller.clock raw slack p q) (PrimeSecondAllCommitCaller.start raw)
      let last ← BitOracleMachine.run PrimeSecondKeyMachine.code (PrimeSecondKeyMachine.clock p)
        (PrimeSecondKeyMachine.start first.1.stk)
      pure (BitOracleReturnLink.embed tailLabel none last.1,first.2+last.2)) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  have hframe := BitOracleStackFrame.run prefixLayout PrimeSecondAllCommitCaller.code
    (PrimeSecondAllCommitCaller.clock raw slack p q) (PrimeSecondAllCommitCaller.start raw) (fun _ => [])
  change BitOracleMachine.run prefixCode (PrimeSecondAllCommitCaller.clock raw slack p q)
    (BitOracleStackFrame.embed prefixLayout (PrimeSecondAllCommitCaller.start raw) (fun _ => [])) = _ at hframe
  have hh : ∀ out ∈ support (BitOracleMachine.run prefixCode
      (PrimeSecondAllCommitCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeSecondAllCommitCaller.start raw) (fun _ => []))), out.1.l = none := by
    rw [hframe]
    intro out ho
    obtain ⟨first,hf,rfl⟩ := mem_support_map_peel _ _ ho
    exact (PrimeSecondAllCommitCaller.run_support slack g pk vote s live first hf).1
  have ht : ∀ out ∈ support (BitOracleMachine.run prefixCode
      (PrimeSecondAllCommitCaller.clock raw slack p q)
      (BitOracleStackFrame.embed prefixLayout (PrimeSecondAllCommitCaller.start raw) (fun _ => []))),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondKeyMachine.clock p)
        (BitOracleReturnLink.embed prefixLabel (some (tailLabel 0)) out.1)), last.1.l = none := by
    rw [hframe]
    intro out ho
    obtain ⟨first,hf,he⟩ := mem_support_map_peel _ _ ho
    subst out
    change ∀ last ∈ support (BitOracleMachine.run code (PrimeSecondKeyMachine.clock p)
      (BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
        (BitOracleStackFrame.embed prefixLayout first.1 (fun _ => [])))), last.1.l = none
    rw [supported_return slack g pk vote s live first hf,
      BitOracleReturnLink.rename_run _ _ _ tail_code]
    intro last hl
    obtain ⟨out,hout,rfl⟩ := mem_support_map_peel _ _ hl
    have hh := (tail_bound slack g pk vote s live first hf out hout).1
    change out.1.l.elim none (some ∘ tailLabel) = none
    rw [hh]
    rfl
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code _ _ _ hh ht,hframe]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]
  apply bind_congr_of_forall_mem_support
  intro first hf
  rw [supported_return slack g pk vote s live first hf,
    BitOracleReturnLink.rename_run _ _ _ tail_code]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- Every supported raw result halts within the derived prefix plus p1 key serialization
cost. The full retained state and new draws are identified by execution_source. -/
theorem run_support {p q : Nat} [Fact p.Prime] [Fact q.Prime] (slack : Nat)
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    ∀ out ∈ support (BitOracleMachine.run code
      (clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)))),
      out.1.l = none ∧ out.2 ≤ cost (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q := by
  rw [linked_run]
  intro out ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨first,hf,ho⟩ := ho
  rw [mem_support_bind_iff] at ho
  obtain ⟨last,hl,ho⟩ := ho
  have he := eq_of_mem_support_pure _ ho
  subst out
  have hp := PrimeSecondAllCommitCaller.run_support slack g pk vote s live first hf
  have ht := tail_bound slack g pk vote s live first hf last hl
  constructor
  · change last.1.l.elim none (some ∘ tailLabel) = none
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
    (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    BitOracleLoopBounded.Within limit
      (cost (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (BitOracleMachine.run code
        (clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
        (start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)))) := by
  exact within_support limit _ _ (run_support slack g pk vote s live)

#print axioms linked_run
#print axioms run_support
#print axioms within
end ExplainableCrypto.Helios.Computational.PrimeSecondKeyCaller
