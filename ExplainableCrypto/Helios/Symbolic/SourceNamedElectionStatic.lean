import ExplainableCrypto.Helios.Symbolic.SourceNamedFreshStatic
import Mathlib.Logic.Relation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat} {a b d : Named (Fin handles)}

theorem RepresentsFrame.internal_star {φ : Frame restricted handles}
    (h : a.RepresentsFrame hidden φ) (hs : Relation.ReflTransGen Reduction a b) : b.RepresentsFrame hidden φ := by
  induction hs with
  | refl => exact h
  | tail hs hstep ih => exact ih.internal hstep

theorem StaticEq.internal_star_left (h : StaticEq a d) (hs : Relation.ReflTransGen Reduction a b) :
    StaticEq b d := by
  obtain ⟨hidden,restricted,φ,ψ,hφ,hψ,he⟩ := h
  exact .of_presentations (hφ.internal_star hs) hψ he

/-- Every reached stage supplies Definition 1 witnesses at the actual Named
source layer, using B7/B8's complete equality observations. This is the static
clause only; matching arbitrary Named actions remains separate. -/
theorem reachable_source_staticEq {n : Nat} {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {phase : Process.Phase}
    (h : Process.Reachable ns false left right extra phase) (ch : Channels) :
    StaticEq (restrictedState ch.privateChannels (sourceState ns false left right extra ch phase))
      (restrictedState ch.privateChannels (sourceState ns true left right extra ch phase)) :=
  restrictedState_staticEq_of_frames _ _ (reachable_source_view_staticEq hf h)

/-- Arbitrary actual structural representatives inherit the reached stage's
full static witness, even if their named syntax is not canonical. -/
theorem reachable_structural_source_staticEq {n : Nat} {ns : Names n} (hf : ns.Fresh)
    {left right : CandidateSubstitution n Empty} {extra : Nat} {phase : Process.Phase}
    (h : Process.Reachable ns false left right extra phase) (ch : Channels)
    {a b : Named (Fin phase.handles)}
    (ha : Structural (restrictedState ch.privateChannels (sourceState ns false left right extra ch phase)) a)
    (hb : Structural (restrictedState ch.privateChannels (sourceState ns true left right extra ch phase)) b) :
    StaticEq a b := (reachable_source_staticEq hf h ch).structural ha hb

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
