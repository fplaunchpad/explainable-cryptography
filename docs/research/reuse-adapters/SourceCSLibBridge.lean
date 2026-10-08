import ExplainableCrypto.Helios.Symbolic.SourceBallotSecrecy
import CSLibComposition

/-! Retrospective adapter only: package the original source actions for CSLib.
Every step below contains an original Named derivation. B9 supplies matching;
full frame observations and finite handle domains remain explicit. -/
namespace HeliosReuseAudit.SourceCSLibBridge
open ExplainableCrypto.Helios.Symbolic Historical General Source

structure State where
  handles : Nat
  body : Named (Fin handles)

inductive Label where
  | tau
  | free (handles : Nat) (action : Extended.FreeLabel (Fin handles))
  | bound (handles channel : Nat)
instance : Cslib.HasTau Label := ⟨Label.tau⟩

inductive Step : State → Label → State → Prop where
  | internal {h} {a b : Named (Fin h)} (step : Named.Reduction a b) :
      Step ⟨h,a⟩ .tau ⟨h,b⟩
  | free {h} {a b : Named (Fin h)} {l} (scope : a.LabelScoped l)
      (step : Named.FreeStep a l b) : Step ⟨h,a⟩ (.free h l) ⟨h,b⟩
  | bound {h} {a : Named (Fin h)} {b : Named (Option (Fin h))} {c}
      (step : Named.BoundOutput a c b) :
      Step ⟨h,a⟩ (.bound h c) ⟨h+1,b.rename Extended.outputHandle⟩

def lts : Cslib.LTS State Label := ⟨Step⟩

inductive Observes : State → State → Prop where
  | mk {h} {a b : Named (Fin h)} (equiv : Named.StaticEq a b) :
      Observes ⟨h,a⟩ ⟨h,b⟩

theorem Observes.trans {a b c} (hab : Observes a b) (hbc : Observes b c) :
    Observes a c := by
  cases hab
  cases hbc
  exact .mk (Named.StaticEq.trans ‹_› ‹_›)

variable {n : Nat}
inductive Related (origin : Bool → Named (Fin 1)) (ns : Names n)
    (left right : CandidateSubstitution n Empty) (extra : Nat) (ch : Channels) :
    State → State → Prop where
  | mk {h} {a b : Named (Fin h)}
      (related : SourceElectionRelation origin ns left right extra ch a b) :
      Related origin ns left right extra ch ⟨h,a⟩ ⟨h,b⟩

variable {origin : Bool → Named (Fin 1)} {ns : Names n}
  {left right : CandidateSubstitution n Empty} {extra : Nat} {ch : Channels}
local notation "R" => Related origin ns left right extra ch

theorem Related.symm {a b} (hr : R a b) : R b a := by
  cases hr with | mk hr => exact .mk hr.symm

theorem match_step (hf : ns.Fresh) (hc : ch.Fresh)
    {a b a' l} (hr : R a b) (ha : Step a l a') :
    ∃ b', Step b l b' ∧ R a' b' := by
  cases hr with
  | mk hr =>
    cases ha with
    | internal ha =>
      obtain ⟨b',hb,ht⟩ := hr.internal hf hc ha
      exact ⟨_,.internal hb,.mk ht⟩
    | free _ ha =>
      obtain ⟨b',hb,ht⟩ := hr.free hf hc ha
      exact ⟨_,.free (Named.labelScoped_of_all_exports _ _
        (hr.staticEq hf).complete_domains.2) hb,.mk ht⟩
    | bound ha =>
      obtain ⟨b',hb,ht⟩ := hr.bound hf hc ha
      exact ⟨_,.bound hb,.mk ht⟩

theorem related_is_framed (hf : ns.Fresh) (hc : ch.Fresh) :
    CSLibComposition.FramedWeak lts State.handles Observes R := by
  constructor
  · apply Cslib.LTS.IsSWBisimulation.isWeakBisimulation
    intro a b hr l
    constructor
    · intro a' ha
      obtain ⟨b',hb,ht⟩ := match_step hf hc hr ha
      exact ⟨b',Cslib.LTS.STr.single hb,ht⟩
    · intro b' hb
      obtain ⟨a',ha,ht⟩ := match_step hf hc hr.symm hb
      exact ⟨a',Cslib.LTS.STr.single ha,ht.symm⟩
  · intro a b hr; cases hr; rfl
  · intro a b hr; cases hr with | mk hr => exact .mk (hr.staticEq hf)

/-- Upstream composition now applies to the actual source transition system;
B9 and full Named observations remain load-bearing dependencies. -/
theorem source_composition_is_framed (hf : ns.Fresh) (hc : ch.Fresh) :
    CSLibComposition.FramedWeak lts State.handles Observes (Relation.Comp R R) :=
  CSLibComposition.comp Observes.trans (related_is_framed hf hc) (related_is_framed hf hc)

/-- The same historical freshness assumptions construct the source witness. -/
theorem actual_scoped_pair_has_cslib_witness (ns : Names n) (hf : ns.Fresh)
    (left right : CandidateSubstitution n Empty) (hl : NoncesFreshFor ns left.value)
    (hr : NoncesFreshFor ns right.value) (extra : Nat) (ch : Channels) (hc : ch.Fresh) :
    let rel := Related (fun s => scopedVoterElection ns s left right extra ch) ns left right extra ch
    CSLibComposition.FramedWeak lts State.handles Observes rel ∧
    rel ⟨1,scopedVoterElection ns false left right extra ch⟩
        ⟨1,scopedVoterElection ns true left right extra ch⟩ :=
  ⟨related_is_framed hf hc,.mk (SourceElectionRelation.initial ns hf false true left right hl hr extra ch)⟩

/-- Fresh publication adds exactly one coordinate; it cannot retain the old domain. -/
theorem bound_changes_domain {a b : State} {h c} (hs : Step a (.bound h c) b) :
    b.handles = a.handles + 1 ∧ b.handles ≠ a.handles := by
  cases hs
  exact ⟨rfl,by dsimp; omega⟩

#print axioms Observes.trans
#print axioms match_step
#print axioms related_is_framed
#print axioms source_composition_is_framed
#print axioms actual_scoped_pair_has_cslib_witness
#print axioms bound_changes_domain
end HeliosReuseAudit.SourceCSLibBridge
