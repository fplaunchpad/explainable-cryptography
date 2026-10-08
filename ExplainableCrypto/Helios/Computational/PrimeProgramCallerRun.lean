import ExplainableCrypto.Helios.Computational.PrimeProgramCaller
import ExplainableCrypto.Helios.Computational.PrimeProgramMachineRun

namespace ExplainableCrypto.Helios.Computational.PrimeProgramCaller
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
    (first : PrimeProgrammedStateCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeProgrammedStateCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    ∃ out : (ZMod q × ZMod q) × (ZMod q × ZMod q × ZMod q × ZMod q),
      first.1 = PrimeProgrammedStateCaller.sourceResult slack g pk vote s live out ∧
      first.2 ≤ PrimeProgrammedStateCaller.cost (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q := by
  have hm : first.1 ∈ support (Prod.fst <$> BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeProgrammedStateCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)))) := by
    rw [support_map]
    exact ⟨first,hf,rfl⟩
  rw [PrimeProgrammedStateCaller.execution_source,simulateQ_map] at hm
  obtain ⟨out,_,ho⟩ := mem_support_map_peel _ _ hm
  exact ⟨out,ho,(PrimeProgrammedStateCaller.run_support slack g pk vote s live first hf).2⟩

private theorem supported_return {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (first : PrimeProgrammedStateCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeProgrammedStateCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    BitOracleReturnLink.embed prefixLabel (some (tailLabel 0))
      first.1 =
    BitOracleReturnLink.embed tailLabel none (PrimeProgramMachine.start first.1.stk) := by
  obtain ⟨out,he,_⟩ := prefix_support slack g pk vote s live first hf
  rw [he]
  exact prefix_return _

private theorem tail_bound {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q))
    (first : PrimeProgrammedStateCaller.Config × Nat)
    (hf : first ∈ support (BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)) slack p q)
      (PrimeProgrammedStateCaller.start (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live))))) :
    ∀ last ∈ support (BitOracleMachine.run PrimeProgramMachine.code (PrimeProgramMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
      (PrimeProgramMachine.start first.1.stk)),
      last.1.l = none ∧ last.2 ≤ PrimeProgramMachine.cost p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length := by
  obtain ⟨out,he,_⟩ := prefix_support slack g pk vote s live first hf
  obtain ⟨c,hc,hr⟩ := PrimeProgramMachine.charged_source slack g pk vote s live out
  rw [he,hr]
  intro last hl
  have he := eq_of_mem_support_pure _ hl
  subst last
  exact ⟨rfl,hc⟩

/-- One actual raw execution executes the existing prefix and returns live to
the programmed-state controller, preserving both query trees and actual charges. -/
theorem linked_run {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (slack : Nat) (g pk : PrimeGroup p q) (vote : Bool) (s : BallotFiniteProgrammedState (ZMod q) (PrimeGroup p q))
    (live : BallotFiniteCache (ZMod q) (PrimeGroup p q)) :
    let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
    BitOracleMachine.run code (clock raw slack p q) (start raw) = (do
      let first ← BitOracleMachine.run PrimeProgrammedStateCaller.code
        (PrimeProgrammedStateCaller.clock raw slack p q) (PrimeProgrammedStateCaller.start raw)
      let last ← BitOracleMachine.run PrimeProgramMachine.code (PrimeProgramMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
        (PrimeProgramMachine.start first.1.stk)
      pure (BitOracleReturnLink.embed tailLabel none last.1,first.2+last.2)) := by
  dsimp only
  let raw := PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)
  have hh : ∀ out ∈ support (BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock raw slack p q) (PrimeProgrammedStateCaller.start raw)),
      out.1.l = none := by
    intro out ho
    exact (PrimeProgrammedStateCaller.run_support slack g pk vote s live out ho).1
  have ht : ∀ out ∈ support (BitOracleMachine.run PrimeProgrammedStateCaller.code
      (PrimeProgrammedStateCaller.clock raw slack p q) (PrimeProgrammedStateCaller.start raw)),
      ∀ last ∈ support (BitOracleMachine.run code (PrimeProgramMachine.clock p q (PrimeHonestInputMachine.input g pk slack vote (PrimeProgrammedStateSource.saved s live)).length)
        (BitOracleReturnLink.embed prefixLabel (some (tailLabel 0)) out.1)),
        last.1.l = none := by
    intro first hf
    rw [supported_return slack g pk vote s live first hf,
      BitOracleReturnLink.rename_run _ _ _ tail_code]
    intro last hl
    obtain ⟨sourceOut,hs,_⟩ := prefix_support slack g pk vote s live first hf
    obtain ⟨charge,_,hr⟩ := PrimeProgramMachine.charged_source slack g pk vote s live sourceOut
    rw [hs,hr,map_pure] at hl
    have he := eq_of_mem_support_pure _ hl
    rw [he]
    rfl
  change BitOracleMachine.run code (_+_) (BitOracleReturnLink.embed prefixLabel _ _) = _
  rw [BitOracleReturnLink.run _ _ _ _ prefix_code _ _ _ hh ht]
  apply bind_congr_of_forall_mem_support
  intro first hf
  rw [supported_return slack g pk vote s live first hf,
    BitOracleReturnLink.rename_run _ _ _ tail_code]
  simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def]

/-- Every supported raw result halts within the derived sum of actual prefix
and programming costs. Full state is established separately by execution_source. -/
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
  have hp := PrimeProgrammedStateCaller.run_support slack g pk vote s live first hf
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
end ExplainableCrypto.Helios.Computational.PrimeProgramCaller
