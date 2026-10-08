import Cslib.Foundations.Semantics.LTS.Bisimulation

/-! Isolated pinned-CSLib experiment. The LTS and labels are unchanged inputs;
full observations and equal handle domains are additional explicit obligations.
This proves a composition adapter, not a Helios source-LTS translation. The
finished secrecy proof does not use bisimulation composition. -/
namespace HeliosReuseAudit.CSLibComposition
open Cslib
universe u v
variable {State : Type u} {Label : Type v} [HasTau Label]

structure FramedWeak (lts : LTS State Label) (domain : State → Nat)
    (Observe : State → State → Prop) (R : State → State → Prop) : Prop where
  dynamic : LTS.IsWeakBisimulation lts lts R
  domains : ∀ {a b}, R a b → domain a = domain b
  observations : ∀ {a b}, R a b → Observe a b

/-- Retains the unchanged transition system, complete observation predicate and
handle domains. Transitivity of the observation predicate remains explicit. -/
theorem comp {lts : LTS State Label} {domain : State → Nat}
    {Observe R S : State → State → Prop}
    (hobs : ∀ {a b c}, Observe a b → Observe b c → Observe a c)
    (hr : FramedWeak lts domain Observe R) (hs : FramedWeak lts domain Observe S) :
    FramedWeak lts domain Observe (Relation.Comp R S) := by
  refine ⟨hr.dynamic.comp hs.dynamic,?_,?_⟩
  · rintro a c ⟨b,hab,hbc⟩
    exact (hr.domains hab).trans (hs.domains hbc)
  · rintro a c ⟨b,hab,hbc⟩
    exact hobs (hr.observations hab) (hs.observations hbc)

inductive Event where
  | tau
  | input (completePayload : Nat)
  | publication
instance : HasTau Event := ⟨Event.tau⟩
def stopped : LTS Bool Event := ⟨fun _ _ _ => False⟩

private theorem stopped_dynamic (R : Bool → Bool → Prop) : LTS.IsWeakBisimulation stopped stopped R := by
  apply LTS.IsSWBisimulation.isWeakBisimulation
  intro a b _ μ
  exact ⟨fun _ h => h.elim,fun _ h => h.elim⟩

/-- Independent literal control: equal states retain their two distinct
observation values and domains through upstream composition. -/
theorem equal_states_compose_with_observations :
    FramedWeak stopped (fun b => if b then 2 else 1) Eq (Relation.Comp Eq Eq) := by
  have he : FramedWeak stopped (fun b => if b then 2 else 1) Eq Eq :=
    ⟨stopped_dynamic Eq,fun h => congrArg (fun b : Bool => if b then (2 : Nat) else 1) h,fun h => h⟩
  exact comp Eq.trans he he

/-- Empty transition systems are dynamically indistinguishable even when
literal observations disagree. The added observation clause detects this. -/
theorem dynamic_only_does_not_preserve_observations :
    LTS.IsWeakBisimulation stopped stopped (fun _ _ => True) ∧
    ¬ FramedWeak stopped (fun _ => 1) Eq (fun _ _ => True) := by
  refine ⟨stopped_dynamic _,?_⟩
  intro h
  have he : false = true := h.observations trivial
  cases he

theorem dynamic_only_does_not_preserve_domains :
    ¬ FramedWeak stopped (fun b => if b then 2 else 1) (fun _ _ => True) (fun _ _ => True) := by
  intro h
  have he : (1 : Nat) = 2 := h.domains (a := false) (b := true) trivial
  omega

#print axioms comp
#print axioms equal_states_compose_with_observations
#print axioms dynamic_only_does_not_preserve_observations
#print axioms dynamic_only_does_not_preserve_domains
#print axioms Cslib.LTS.IsWeakBisimulation.comp
end HeliosReuseAudit.CSLibComposition
