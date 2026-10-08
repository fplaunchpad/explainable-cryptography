import ExplainableCrypto.Helios.Computational.RepairedOutputStorage

/-! Literal field-layout fixtures, independent of cryptographic proof generation.
Actual acceptance/rejection controls remain in RepairedBoardOracleControls. -/
namespace ExplainableCrypto.Helios.Computational.RepairedOutputStorageControls

def ballot : Ballot Nat Nat 2 :=
  ⟨(fun i => if i = 0 then (1,2) else (3,4)),
   (fun i => if i = 0 then ⟨⟨5,6,21,22⟩,⟨7,8,23,24⟩⟩
     else ⟨⟨9,10,25,26⟩,⟨11,12,27,28⟩⟩),
   ⟨⟨13,14,29,30⟩,⟨15,16,31,32⟩⟩⟩

def changed : Ballot Nat Nat 2 :=
  {ballot with overall := {ballot.overall with zero := {ballot.overall.zero with response := 0}}}

/-- Literal expectations fix every ciphertext, commitment, challenge and response
field; matching lengths alone would not establish this layout. -/
theorem literal_records :
    ballotGroupRecord ballot = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] ∧
    ballotScalarRecord ballot = [21,22,23,24,25,26,27,28,29,30,31,32] := by decide

/-- Equal group projections do not discard or hide the changed proof response
when the separate scalar projection is retained. -/
theorem scalar_mutation_observed : ballotGroupRecord changed = ballotGroupRecord ballot ∧
    ballotScalarRecord changed ≠ ballotScalarRecord ballot := by decide

#print axioms literal_records
#print axioms scalar_mutation_observed
end ExplainableCrypto.Helios.Computational.RepairedOutputStorageControls
