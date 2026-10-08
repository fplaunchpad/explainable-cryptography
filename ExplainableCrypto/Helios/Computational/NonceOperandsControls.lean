import ExplainableCrypto.Helios.Computational.NonceOperandsRun

/-! Independently specified predecessor/width boundaries and rejection controls.
The source bit lists retain little-endian digits, suffixes and opaque saved data. -/
namespace ExplainableCrypto.Helios.Computational.NonceOperandsControls
open OracleComp OracleSpec BitOracleMachine NonceOperands
attribute [local implicit_reducible] FreeMonoid PFunctor.Idx PFunctor.FreeM.bind
set_option maxRecDepth 8192

private theorem value (slack q : Nat) (hq : 2 ≤ q) :
    Prod.fst <$> BitOracleMachine.run code (clock slack q) (startWord (SamplerOperands.input slack q [])) =
      pure (result slack q [] (fun _ => [])) := by
  obtain ⟨c,_,h⟩ := charged slack q hq
  rw [h]
  rfl

/-- Public q=2 produces modulus one and exactly one width marker, not the
two-marker width of the original public q. Input is the literal record 011001. -/
theorem two_control :
    Prod.fst <$> BitOracleMachine.run code (clock 0 2)
      (startWord [false,true,true,false,false,true]) =
      pure (⟨none,0,![[],[true],[true],[],[],[],[],[]]⟩ : BitOracleMachine.Config 8 size 3) := by
  exact value 0 2 (by decide)

/-- Borrow across the public binary power boundary 1000 produces 111. Two
slack markers plus the three actual modulus digits give five width markers. -/
theorem borrow_control :
    Prod.fst <$> BitOracleMachine.run code (clock 2 8)
      (startWord [true,true,false,true,true,true,true,false,false,false,false,true]) =
      pure (⟨none,0,![[],[true,true,true],[true,true,true,true,true],[],[],[],[],[]]⟩ :
        BitOracleMachine.Config 8 size 3) := by
  exact value 2 8 (by decide)

/-- The changed program's whole canonical run retains a nonpalindromic suffix
and all three nonempty saved words, including their bit order. -/
theorem suffix_frame_control :
    tick^[clock 1 4]
      (SamplerOperands.start false [true,false,true,true,true,false,false,false,true,false,true,true]
        ![[true,false,true],[false,false,true],[true,true,false]]) =
      SamplerOperands.state none [false,true,true] [true,true] [true,true,true] [] []
        ![[true,false,true],[false,false,true],[true,true,false]] none := by
  exact NonceOperands.run 1 4 (by decide) [false,true,true]
    ![[true,false,true],[false,false,true],[true,true,false]]

/-- Keeping the old public-modulus width fails already at q=2. -/
theorem old_width_not_retained :
    (fun out => out.1.stk 2) <$> BitOracleMachine.run code (clock 0 2)
      (startWord [false,true,true,false,false,true]) ≠ pure [true,true] := by
  have h := congrArg (fun oa : OracleComp spec (BitOracleMachine.Config 8 size 3) =>
    (fun cfg => cfg.stk 2) <$> oa) two_control
  simp only [Functor.map_map,map_pure] at h
  rw [h]
  simp

/-- Zero cannot prepare a positive sampling range. -/
theorem zero_rejected :
    Prod.fst <$> BitOracleMachine.run code (clock 0 0) (startWord [false,false]) =
      pure (⟨none,1,fun _ => []⟩ : BitOracleMachine.Config 8 size 3) := by
  change (pure (⟨none,1,_⟩ : BitOracleMachine.Config 8 size 3) : OracleComp spec _) = _
  congr 2
  funext k; fin_cases k <;> rfl

/-- Public q=1 is rejected after its predecessor becomes zero. -/
theorem one_rejected :
    Prod.fst <$> BitOracleMachine.run code (clock 0 1) (startWord [false,true,false,true]) =
      pure (⟨none,1,fun _ => []⟩ : BitOracleMachine.Config 8 size 3) := by
  change (pure (⟨none,1,_⟩ : BitOracleMachine.Config 8 size 3) : OracleComp spec _) = _
  congr 2
  funext k; fin_cases k <;> rfl

/-- Change only the two predecessor instructions back to the original binary
increment. This is the native campaign's distinct successor-for-predecessor
mutation; parsing, width collection and all other instructions are unchanged. -/
private def incrementMutant : Code 8 size 3 := fun l =>
  if l = 10 ∨ l = 11 then .compute (SamplerOperands.compiled l) else code l

/-- On the smallest valid public modulus q=2, the actual increment mutant
returns modulus three (11) and two width markers, rather than modulus one. -/
theorem increment_mutant_control :
    Prod.fst <$> BitOracleMachine.run incrementMutant (clock 0 2)
      (startWord [false,true,true,false,false,true]) =
      pure (⟨none,0,![[],[true,true],[true,true],[],[],[],[],[]]⟩ :
        BitOracleMachine.Config 8 size 3) := by
  change (pure (⟨none,0,_⟩ : BitOracleMachine.Config 8 size 3) : OracleComp spec _) = _
  congr 2
  funext k; fin_cases k <;> rfl

/-- Observe the executed mutant's modulus, independently of its width: this
rules out silently replacing the intended predecessor by the old increment. -/
theorem increment_mutant_not_predecessor :
    (fun out => out.1.stk 1) <$> BitOracleMachine.run incrementMutant (clock 0 2)
      (startWord [false,true,true,false,false,true]) ≠ pure [true] := by
  have h := congrArg (fun oa : OracleComp spec (BitOracleMachine.Config 8 size 3) =>
    (fun cfg => cfg.stk 1) <$> oa) increment_mutant_control
  simp only [Functor.map_map,map_pure] at h
  rw [h]
  simp

#print axioms two_control
#print axioms borrow_control
#print axioms suffix_frame_control
#print axioms old_width_not_retained
#print axioms zero_rejected
#print axioms one_rejected
#print axioms increment_mutant_control
#print axioms increment_mutant_not_predecessor
end ExplainableCrypto.Helios.Computational.NonceOperandsControls
