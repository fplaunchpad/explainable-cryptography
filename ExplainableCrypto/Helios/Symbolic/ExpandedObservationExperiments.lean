import ExplainableCrypto.Helios.Symbolic.ExpandedAssemblyExperiments
import ExplainableCrypto.Helios.Symbolic.ObservationAssemblyExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedObservationExperiments
open ExplainableCrypto.Testing Historical General ObservationAssemblyExperiments
abbrev names := LocalRootSPOT.names
abbrev left := LocalRootSPOT.left
abbrev right := LocalRootSPOT.right
abbrev world (swap : Bool) := expandedFrame names swap left right []

private def fixtures (seed : Nat) : List (Recipe (ExpandedHandles 1) × Nat) :=
  let a : Recipe (ExpandedHandles 1) := .name (40+seed%3)
  let b : Recipe (ExpandedHandles 1) := .name (50+seed%5)
  let trustee : Recipe (ExpandedHandles 1) := .var (expandedPartial 0)
  let result : Recipe (ExpandedHandles 1) := .var (expandedResult 1)
  let key : Recipe (ExpandedHandles 1) := .var (expandedOld 0)
  let honest : Recipe (ExpandedHandles 1) := .unary .fst (.var (expandedOld 1))
  let cipher := Term.ternary .penc key trustee result
  let e5 := Term.ternary .penc (.unary .pk a) b trustee
  [(a,0),(.const .zero,1),(.unary .pk trustee,2),(.unary .fst trustee,3),
   (.unary .snd trustee,4),(.binary .pair trustee result,5),(.binary .partialDecrypt trustee result,6),
   (.binary .dec a b,7),(.binary .mul trustee result,8),(.binary .add trustee result,9),
   (.binary .compose trustee result,10),(cipher,11),(.ternary .checkspk trustee b result,12),
   (.spk key trustee result cipher,13),(trustee,6),(result,1),(honest,11),
   (.binary .dec a e5,6),(.binary .dec (.binary .partialDecrypt a e5) e5,6),
   (.unary .fst (.binary .pair honest trustee),11),(.binary .mul cipher honest,11)]

def raw_result_head_mutation (_ : Nat) : Bool :=
  let t := (world false).eval (.var (expandedResult 0))
  decide (branch t = branch (normalizeRaw t))

def fusion_head_mutation (_ : Nat) : Bool :=
  let t : Ground := .ternary .penc (.name 40) (.name 50) (.const .zero)
  decide (branch (normalizeRaw (.binary .mul t t)) = 8)

def missing_binding_mutation (_ : Nat) : Bool :=
  let a : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 50) (.const .zero)
  let b : Ground := .ternary .penc (.unary .pk (.name 40)) (.name 51) (.const .zero)
  decide (branch (normalizeRaw (.binary .dec (.binary .partialDecrypt (.name 40) a) b)) = 1)

/-- Fixture oracle: raw reduction followed by the existing E0 numeric summary.
This handles top-level zero/one aliases; it is not a general E decision procedure. -/
def normalizedBranch (t : Ground) : Nat :=
  let u := normalizeRaw t
  let summary := u.addSyntaxSummary
  if summary.atoms = 0 ∧ (summary.numeric = some 0 ∨ summary.numeric = some 1) then 1
  else branch u

def raw_normalization_complete_mutation (_ : Nat) : Bool :=
  let t := (world false).eval (.var (expandedResult 1))
  decide (branch (normalizeRaw t) = normalizedBranch t)

def check (seed : Nat) : Bool :=
  [false,true].all fun swap =>
    (fixtures seed).all fun p => normalizedBranch ((world swap).eval p.1) == p.2


#eval campaign "raw published-result head selects observation branch (negative control)" (∀ n : Nat, raw_result_head_mutation n = true) 1 true
#eval campaign "fused ciphertext remains a normal product (negative control)" (∀ n : Nat, fusion_head_mutation n = true) 1 true
#eval campaign "E6 normal-head selection ignores binding (negative control)" (∀ n : Nat, missing_binding_mutation n = true) 1 true
#eval campaign "raw normalization completes E0 numeric sums (negative control)" (∀ n : Nat, raw_normalization_complete_mutation n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded observation dispatch uses normal values across all fourteen heads" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded observation assembly backstop failed")
  IO.println "expanded observation backstop: 2048 inputs, 21 fixtures each, both swaps, all 14 ground head classes, actual partial/result handles, E5/E6 success, projections and homomorphic fusion"

end ExplainableCrypto.Helios.Symbolic.ExpandedObservationExperiments
