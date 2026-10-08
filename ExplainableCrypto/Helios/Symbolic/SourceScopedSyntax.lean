import ExplainableCrypto.Helios.Symbolic.SourceVisibleReduction

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source

/-- Fixed outer authenticated channels in the finite historical election. -/
def Channels.privateChannels (ch : Channels) : Finset Nat := {ch.voter 0,ch.voter 1,ch.trustee}

/-- An evaluated finite process with all public message bindings retained.
The correspondence to explicit extended active substitutions is still required. -/
structure ScopedState (restricted : Finset Nat) (handles : Nat) where
  frame : Frame restricted handles
  body : Agent Empty

/-- Public labels contain a recipe on input and bind the next fresh handle on
output. Ground output payloads are not part of the public label. -/
inductive PublicEvent : Nat → Nat → Type where
  | tau : PublicEvent handles handles
  | input (channel : Nat) (recipe : Recipe handles) : PublicEvent handles handles
  | output (channel : Nat) : PublicEvent handles (handles+1)

/-- Fixed outer restriction blocks actions on private channels. Tau remains
available there. Public inputs use only currently available public recipes;
outputs append their exact values to the frame without requiring those values
themselves to be public syntax. Scope/active-substitution derivation is separate. -/
inductive ScopedStep (hidden restricted : Finset Nat) :
    {before after : Nat} → ScopedState restricted before → PublicEvent before after →
      ScopedState restricted after → Prop where
  | tau {handles : Nat} (φ : Frame restricted handles) {p q : Agent Empty} (h : Agent.Tau p q) :
      ScopedStep hidden restricted ⟨φ,p⟩ .tau ⟨φ,q⟩
  | input {handles : Nat} (φ : Frame restricted handles) (c : Nat) (r : Recipe handles)
      {p q : Agent Empty} (hc : c ∉ hidden) (hr : r.Public restricted)
      (h : Agent.Visible p (.input c (φ.eval r)) q) :
      ScopedStep hidden restricted ⟨φ,p⟩ (.input c r) ⟨φ,q⟩
  | output {handles : Nat} (φ : Frame restricted handles) (c : Nat) (m : Ground)
      {p q : Agent Empty} (hc : c ∉ hidden) (h : Agent.Visible p (.output c m) q) :
      ScopedStep hidden restricted ⟨φ,p⟩ (.output c) ⟨φ.extend m,q⟩
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
