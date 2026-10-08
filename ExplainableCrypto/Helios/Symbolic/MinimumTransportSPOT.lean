import ExplainableCrypto.Helios.Symbolic.LocalMinimumTransport
import ExplainableCrypto.Helios.Symbolic.MinimumTransportExperiments
import ExplainableCrypto.Helios.Symbolic.PartialDecryptionOrigins

namespace ExplainableCrypto.Helios.Symbolic.MinimumTransportSPOT
open MinimumTransportExperiments

/-- Minimum-pair agreement can miss an arbitrary-recipe observation. This finite
size/equality countermodel is not a frame in the Helios algebra. -/
theorem minimum_tests_need_transport :
    step fixtureSize fixtureSource fixtureTarget = true ∧
    allTests fixtureSource fixtureTarget = false ∧
    shared fixtureSize fixtureSource fixtureTarget = false ∧
    agrees fixtureSource fixtureTarget 0 2 = false := by decide

/-- Shared minimization alone permits the destination to collapse distinct values. -/
theorem transport_needs_minimum_step :
    shared fixtureSize fixtureSource (fun _ => 0) = true ∧
    step fixtureSize fixtureSource (fun _ => 0) = false ∧
    allTests fixtureSource (fun _ => 0) = false := by decide

/-- A changed but injectively renamed destination retains nonconstant observations
and a strictly nonminimum third recipe. -/
theorem finite_shared_lifting :
    let target : Fin 4 → Nat := fun i => if i = 3 then 2 else if i = 1 then 0 else 1
    shared fixtureSize fixtureSource target = true ∧
    step fixtureSize fixtureSource target = true ∧ allTests fixtureSource target = true ∧
    minimum fixtureSize fixtureSource 2 = false ∧ fixtureSource 0 ≠ fixtureSource 1 := by decide

abbrev source : Frame ∅ 1 := ⟨fun _ => .name 70⟩
abbrev destination : Frame ∅ 1 := ⟨fun _ => .name 71⟩
abbrev reveal {V : Type} (t : Term V) : Term V := .unary .fst (.binary .pair t (.const .bottom))

/-- A nonminimum public wrapper has a shared minimum even in distinguishable frames. -/
theorem raw_wrapper_shared :
    (reveal (.name 40) : Recipe 1).Public ∅ ∧
    Frame.SharedMinimum source destination (reveal (.name 40)) ∧
    ¬ MinimalRecipe ∅ source.value (reveal (.name 40)) := by
  have hm : MinimalRecipe ∅ source.value (.name 40) :=
    .of_nodeCount_one (by simp [Term.Public]) rfl
  refine ⟨by simp [Term.Public], .of_recipe_eqE hm (RootStep.fst _ _).sound, ?_⟩
  intro h
  exact h.no_smaller hm.isPublic ((RootStep.fst _ _).sound.subst source.value) (by decide)

/-- The same public handle/name observation separates these actual frames. -/
theorem raw_wrapper_does_not_prove_privacy : ¬ Frame.StaticEq source destination := by
  intro h
  have he := (h (.var 0) (.name 70) trivial (by simp [Term.Public])).1 (.refl _)
  have hn := (EqE.name_iff 71 70).1 he
  omega

/-- The complete local lifting theorem is inhabited and retains distinct public
observations. This diagonal fixture does not establish a vote swap. -/
theorem local_lifting_instance : Frame.StaticEq source source ∧
    ¬ EqE (source.eval (.name 40)) (source.eval (.name 41)) := by
  refine ⟨Frame.staticEq_of_local_minimum_transport ?_ ?_, ?_⟩
  · intro r hp _
    obtain ⟨m, hm, he⟩ := exists_minimal_recipe (σ := source.value) r hp
    exact ⟨m, hm, he, he⟩
  · intro _ _ _ _ _
    rfl
  · intro he
    have hn := (EqE.name_iff 40 41).1 he
    omega

abbrev emptyFrame : Frame ∅ 0 := ⟨Fin.elim0⟩
abbrev minimumPair : Recipe 0 := .binary .pair (.name 40) (.name 41)
abbrev child : Recipe 0 := .binary .pair (reveal (.name 40)) (.name 41)
abbrev parent : Recipe 0 := .unary .fst child

private theorem atomic_value {r : Recipe 0} (h : r.nodeCount ≤ 1) :
    Irreducible (emptyFrame.eval r) ∧ (emptyFrame.eval r).headTag ≠ .binary .pair := by
  rcases r.nodeCount_one_cases h with ⟨a, rfl⟩ | ⟨v, rfl⟩ | ⟨c, rfl⟩
  · exact ⟨name_irreducible a, by simp [Frame.eval, Term.subst, Term.headTag]⟩
  · exact Fin.elim0 v
  · exact ⟨constant_irreducible c, by cases c <;> simp [Frame.eval, Term.subst, Term.headTag]⟩

/-- No atomic or unary-atomic recipe can produce the pair, even modulo full E. -/
theorem literal_pair_minimum : MinimalRecipe ∅ emptyFrame.value minimumPair := by
  refine ⟨by simp [Term.Public], ?_⟩
  intro s _ he
  by_contra hsize
  have htwo : s.nodeCount ≤ 2 := by change ¬ 3 ≤ s.nodeCount at hsize; omega
  rcases s.nodeCount_two_cases htwo with ha | ⟨f, a, rfl, ha⟩
  · obtain ⟨hi, hn⟩ := atomic_value ha
    obtain ⟨_, _, hh, _⟩ := he.passive_binary_irreducible_shape (Or.inl rfl) hi
    exact hn (by change (s.subst emptyFrame.value).headTag = _; rw [hh]; rfl)
  · obtain ⟨hi, hn⟩ := atomic_value ha
    have he' : EqE (.unary f (emptyFrame.eval a)) (.binary .pair (.name 40) (.name 41)) := he.symm
    cases f with
    | pk => exact pk_not_eqE_pair _ _ _ he'
    | fst =>
      obtain ⟨_, _, hp, _⟩ := he'.projection_pair_inversion (Or.inl rfl)
      exact hn (hi.reducesModulo hp).head_eq
    | snd =>
      obtain ⟨_, _, hp, _⟩ := he'.projection_pair_inversion (Or.inr rfl)
      exact hn (hi.reducesModulo hp).head_eq

/-- A real minimum replacement costs 9 nodes to compare, exceeding the original
8-node observation, although the replaced child is strictly smaller than its parent. -/
theorem child_comparison_exceeds_budget :
    child.Public ∅ ∧ MinimalRecipe ∅ emptyFrame.value minimumPair ∧
    EqE (emptyFrame.eval child) (emptyFrame.eval minimumPair) ∧
    EqE (emptyFrame.eval parent) (emptyFrame.eval (.name 40)) ∧
    child.nodeCount < parent.nodeCount ∧
    child.nodeCount + minimumPair.nodeCount = 9 ∧
    parent.nodeCount + (Term.name (V := Fin 0) 40).nodeCount = 8 := by
  have he : EqE child minimumPair := .binary .pair (RootStep.fst _ _).sound (.refl _)
  refine ⟨by simp [Term.Public], literal_pair_minimum, he.subst emptyFrame.value,
    ?_, by decide, by decide, by decide⟩
  exact ((EqE.unary .fst he).trans (RootStep.fst _ _).sound).subst emptyFrame.value

end ExplainableCrypto.Helios.Symbolic.MinimumTransportSPOT
