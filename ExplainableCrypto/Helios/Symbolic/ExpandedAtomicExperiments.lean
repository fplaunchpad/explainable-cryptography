import ExplainableCrypto.Helios.Symbolic.ExpandedOriginExperiments

namespace ExplainableCrypto.Helios.Symbolic.ExpandedAtomicExperiments
open ExplainableCrypto.Testing Historical General
abbrev world (swap : Bool) := expandedFrame LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []

def forceLiteral (_ : Nat) : Bool :=
  let r : Recipe (ExpandedHandles 1) := .var (expandedResult 0)
  decide ((normalizeRaw ((world false).eval r)).addSyntaxSummary = AddSummary.number 0) && decide (r = .const .zero)

def arbitraryDestination (_ : Nat) : Bool :=
  let src : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .const .zero⟩
  let dst : Frame (∅ : Finset Nat) 1 := ⟨fun _ => .const .one⟩
  normalizeRaw (src.eval (.var 0)) == normalizeRaw (dst.eval (.var 0))

def check (seed : Nat) : Bool :=
  let φ := world false
  let ψ := world true
  let pub := 40+seed%11
  let atoms : List (Recipe (ExpandedHandles 1)) := [.name pub,.name (pub+1),.const .zero,.const .one,
    .const .ok,.const .bottom,.var (expandedResult 0),.var (expandedResult 1)]
  decide ((normalizeRaw (φ.eval (.var (expandedResult 0)))).addSyntaxSummary = AddSummary.number 0) &&
  decide ((normalizeRaw (φ.eval (.var (expandedResult 1)))).addSyntaxSummary = AddSummary.number 1) &&
  atoms.all (fun a =>
    decide ((normalizeRaw (φ.eval a)).addSyntaxSummary = (normalizeRaw (ψ.eval a)).addSyntaxSummary) &&
    atoms.all (fun b => decide (decide ((normalizeRaw (φ.eval a)).addSyntaxSummary = (normalizeRaw (φ.eval b)).addSyntaxSummary) =
      decide ((normalizeRaw (ψ.eval a)).addSyntaxSummary = (normalizeRaw (ψ.eval b)).addSyntaxSummary))))

#eval campaign "published atomic minima must be literals (negative control)" (∀ n : Nat, forceLiteral n = true) 1 true
#eval campaign "atomic result transfers to arbitrary destination (negative control)" (∀ n : Nat, arbitraryDestination n = true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "expanded literal and result atoms preserve every comparison" (∀ n : Nat, check n = true) seed
  unless (List.range 2048).all check do
    throw (IO.userError "expanded atomic backstop failed")
  IO.println "expanded atomic backstop: 2048 inputs, eight atomic recipes, all ordered comparisons"

end ExplainableCrypto.Helios.Symbolic.ExpandedAtomicExperiments
