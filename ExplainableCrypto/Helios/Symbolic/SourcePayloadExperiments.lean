import ExplainableCrypto.Helios.Symbolic.RewriteExperiments
import ExplainableCrypto.Helios.Symbolic.SourcePayloadSyntax
import ExplainableCrypto.Helios.Symbolic.HistoricalProcessExperiments
import ExplainableCrypto.Helios.Symbolic.LocalRootSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourcePayloadExperiments
open ExplainableCrypto.Testing Historical General Source

private def body (seed : Nat) : Term (Option Nat) :=
  let t := RewriteExperiments.generatedTerm (seed%4) (seed+13)
  t.subst (fun v => if v%2=0 then .var none else .var (some (v/2)))
private def message (seed : Nat) : Term Nat := RewriteExperiments.generatedTerm (seed%4) (seed+31)
private def env (v : Nat) : Term Nat := .binary .pair (.name (40+v)) (.var (v+2))

def bindingCheck (seed : Nat) : Bool :=
  let b := body seed
  let m := message seed
  decide ((bindInput b m).subst env = b.subst (extendEnv env (m.subst env))) &&
  decide (bindInput (b.subst (liftSubst env)) (m.subst env) = (bindInput b m).subst env)

/-- Explicitly separated public and private variables exercise local flattening. -/
def flattenCheck (seed : Nat) : Bool :=
  let b : Term (Fin 3 ⊕ Nat) := .spk (.var (.inl 0)) (.var (.inr seed))
    (.binary .pair (.var (.inl 1)) (.var (.inr (seed+1)))) (.var (.inl 2))
  let locals := fun i : Nat => (message i).subst (fun v => Term.var (⟨v%3,Nat.mod_lt _ (by decide)⟩ : Fin 3))
  let φ := frame LocalRootSPOT.names false LocalRootSPOT.left LocalRootSPOT.right
  decide (φ.eval (b.subst (flattenLocals locals)) =
    b.subst (Sum.elim φ.value (fun v => φ.eval (locals v))))

def payloadCheck (seed : Nat) : Bool :=
  let rs := (List.range (seed%5)).map (fun i => ElectionTallyExperiments.publicBallot (40+i)
    (if (seed+i)%2=0 then .zero else .one))
  [false,true].all fun swap =>
    let ns := ProofObservationSPOT.oneNames
    let l := ProofObservationSPOT.oneLeft
    let r := ProofObservationSPOT.oneRight
    let out := sourceResults ns swap l r rs
    let expected := 1+((List.range (seed%5)).map (fun i => (seed+i)%2)).sum
    decide ((normalizeRaw (out.project 0)).addSyntaxSummary=AddSummary.number expected) &&
    (normalizeRaw (sourcePartials ns swap l r rs) == normalizeRaw (candidateTuple (tallyPartial ns swap l r rs))) &&
    [0,1].all (fun j : Fin 2 =>
      decide ((normalizeRaw ((sourceResults LocalRootSPOT.names swap LocalRootSPOT.left LocalRootSPOT.right []).project j.val)).addSyntaxSummary
        =AddSummary.number j.val))

/-- Deliberately capture an old free variable with the incoming message. -/
def capturesOld (_ : Nat) : Bool :=
  let b : Term (Option Nat) := .binary .pair (.var none) (.var (some 7))
  decide (b.subst (fun _ => Term.const (V := Nat) .one) = bindInput b (.const .one))

def changesPublic (_ : Nat) : Bool :=
  let b : Term (Fin 3 ⊕ Nat) := .var (.inl 1)
  let wrong : Fin 3 ⊕ Nat → Recipe 3 := fun _ => .const .zero
  decide (b.subst wrong = b.subst (flattenLocals (fun _ => .const .zero)))

/-- Two different tallies detect the abbreviated repeated-last-index defect. -/
def repeatsLastTally (_ : Nat) : Bool :=
  let ns := LocalRootSPOT.names
  let l := LocalRootSPOT.left
  let r := LocalRootSPOT.right
  let tally := sourceTallies ns false l r []
  let parts := sourcePartials ns false l r []
  let wrong := candidateTuple (n := 1) (fun j => Term.binary .dec (parts.project j.val) (tally.project 1))
  normalizeRaw wrong == normalizeRaw (sourceResults ns false l r [])

#eval campaign "source input captures an old variable (negative control)" (∀ n : Nat, capturesOld n=true) 1 true
#eval campaign "source private flattening changes a public handle (negative control)" (∀ n : Nat, changesPublic n=true) 1 true
#eval campaign "source result repeats the last tally (negative control)" (∀ n : Nat, repeatsLastTally n=true) 1 true
#eval do
  for seed in [1,7,42] do
    campaign "source input binding, local flattening and actual private payloads"
      (∀ n : Nat, bindingCheck n && flattenCheck n && payloadCheck n=true) seed
  unless (List.range 2048).all (fun n => bindingCheck n && flattenCheck n && payloadCheck n) do
    throw (IO.userError "source payload backstop failed")
  IO.println "source payload backstop: 2048 inputs, nested bindings/locals, one/two candidates, zero through four extra ballots, both swaps"

end ExplainableCrypto.Helios.Symbolic.SourcePayloadExperiments
