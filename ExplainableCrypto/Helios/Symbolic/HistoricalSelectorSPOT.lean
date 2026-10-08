import ExplainableCrypto.Helios.Symbolic.SmallRecipeBounds
import ExplainableCrypto.Helios.Symbolic.HistoricalValidity
import ExplainableCrypto.Helios.Symbolic.HistoricalFrameSPOT
import Mathlib.Tactic.FinCases

namespace ExplainableCrypto.Helios.Symbolic.HistoricalSelectorSPOT
open Historical

abbrev ns := HistoricalFrameSPOT.names
abbrev σ : Fin 3 → Ground := (frame ns false 0 1).value
abbrev second : Recipe 3 := .unary .fst (.unary .snd (.var 1))
abbrev target : Ground := .ternary .penc (.unary .pk (.name 10)) (.name 21) (.const .zero)
abbrev first0 : Ground := ciphertext ns 0 0 0
abbrev first1 : Ground := ciphertext ns 1 1 0
abbrev rest0 : Ground := Term.tuple ((ballotFields ns 0 0).drop 2)
abbrev rest1 : Ground := Term.tuple ((ballotFields ns 1 1).drop 2)
abbrev tail0 : Ground := .binary .pair target rest0
abbrev tail1 : Ground := .binary .pair (ciphertext ns 1 1 1) rest1

private theorem key_irreducible : Irreducible (publicKey ns) := by
  intro t ht
  obtain ⟨a, ha, _⟩ := ht.pk_cases
  exact name_irreducible 10 a ha

private theorem pair_ne_target (a b : Ground) : ¬ EqE (.binary .pair a b) target :=
  fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ a b h.symm

private theorem first0_ne_target : ¬ EqE first0 target := by
  intro he
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp he).2.1
  have hh := (EqE.name_iff 20 21).mp hn
  cases hh

private theorem first1_ne_target : ¬ EqE first1 target := by
  intro he
  have hn := ((EqE.penc_iff _ _ _ _ _ _).mp he).2.1
  have hh := (EqE.name_iff 22 21).mp hn
  cases hh

private theorem handles_not_ciphertext (k r m : Ground) (v : Fin 3) :
    ¬ EqE (σ v) (.ternary .penc k r m) := by
  fin_cases v
  · exact pk_not_eqE_penc _ _ _ _
  · exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m first0 tail0 h.symm
  · exact fun h => penc_not_eqE_passive_binary .pair (Or.inl rfl) k r m first1 tail1 h.symm

private theorem handle_ne_target (v : Fin 3) : ¬ EqE (σ v) target :=
  handles_not_ciphertext _ _ _ v

private theorem unary_handle_ne_target (f : Unary) (v : Fin 3) :
    ¬ EqE (.unary f (σ v)) target := by
  cases f with
  | pk => exact pk_not_eqE_penc _ _ _ _
  | fst =>
    fin_cases v
    · exact projection_not_eqE_penc_of_irreducible key_irreducible (by decide) .fst
    · intro h
      exact first0_ne_target ((RootStep.fst first0 tail0).sound.symm.trans h)
    · intro h
      exact first1_ne_target ((RootStep.fst first1 tail1).sound.symm.trans h)
  | snd =>
    fin_cases v
    · exact projection_not_eqE_penc_of_irreducible key_irreducible (by decide) .snd
    · intro h
      exact pair_ne_target target rest0 ((RootStep.snd first0 tail0).sound.symm.trans h)
    · intro h
      exact pair_ne_target (ciphertext ns 1 1 1) rest1
        ((RootStep.snd first1 tail1).sound.symm.trans h)

/-- All recipes for the second ciphertext require three nodes, even allowing every name. -/
theorem second_ciphertext_size_bound (r : Recipe 3) (he : EqE (r.subst σ) target) :
    3 ≤ r.nodeCount :=
  ciphertext_recipe_size_ge_three σ _ _ _ handle_ne_target unary_handle_ne_target he

/-- Independent nonce 21 identifies the second ciphertext, not the first ciphertext. -/
theorem second_evaluation : EqE (second.subst σ) target := by
  exact (EqE.unary .fst (RootStep.snd first0 tail0).sound).trans
    (RootStep.fst target rest0).sound

/-- Both actual selector contractions are retained as reachable paths. -/
theorem second_evaluation_reduces : ReducesModulo (second.subst σ) target :=
  (ReducesModulo.single ((RootStep.snd first0 tail0).to_modulo.context (.unary .fst .hole))).trans
    (.single (RootStep.fst target rest0).to_modulo)

/-- Minimality holds under any name policy; this recipe itself names no atoms. -/
theorem second_minimal (restricted : Finset Nat) : MinimalRecipe restricted σ second := by
  refine ⟨trivial, ?_⟩
  intro r _ he
  exact second_ciphertext_size_bound r (he.symm.trans second_evaluation)

/-- The selected ciphertext is a modulo-E0 normal form. -/
theorem target_irreducible : Irreducible target := by
  intro t ht
  rcases ht.penc_cases with ⟨k, hk, _⟩ | ⟨r, hr, _⟩ | ⟨m, hm, _⟩
  · exact key_irreducible k hk
  · exact name_irreducible 21 r hr
  · exact constant_irreducible .zero m hm

/-- Normalizing the argument cannot make the normalized result retain the outer fst. -/
theorem normalized_outer_head_changes :
    Irreducible target ∧
      ∃ a, ReducesModulo ((Term.unary .snd (.var 1) : Recipe 3).subst σ) a ∧
        Irreducible a ∧ ¬ BaseEq target (.unary .fst a) := by
  obtain ⟨a, ha, hi⟩ := exists_normal_form ((Term.unary .snd (.var 1) : Recipe 3).subst σ)
  refine ⟨target_irreducible, a, ha.to_modulo, hi, ?_⟩
  intro he
  cases he.head_eq

/-- The literal single-binary-selector reading of the source exception is false. -/
theorem single_selector_exception_refuted :
    MinimalRecipe ns.nonceNames σ second ∧
      ¬ (∃ f v, second = .unary f (.var v)) ∧
      EqE (second.subst σ) target ∧
      ¬ BaseEq (second.subst σ) target := by
  refine ⟨second_minimal _, ?_, second_evaluation, ?_⟩
  · rintro ⟨f, v, h⟩
    cases h
  · intro h
    cases h.head_eq

/-- A faithful indexed projection exception includes the second-field witness. -/
theorem indexed_projection_exception_applies :
    second = (Term.var 1 : Recipe 3).project 1 ∧
      second.nodeCount = 3 ∧
      (.unary .snd (.var 1) : Recipe 3) = (Term.var 1).drop 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A single-selector first-field access is valid, with its distinct allocated nonce. -/
theorem first_selector_control :
    EqE ((Term.unary .fst (.var 1) : Recipe 3).subst σ) first0 ∧
      ¬ EqE first0 target :=
  ⟨(RootStep.fst first0 tail0).sound, first0_ne_target⟩

/-- The size-three theorem needs its unary-handle premise: the first field takes two nodes. -/
theorem first_selector_minimal (restricted : Finset Nat) :
    MinimalRecipe restricted σ (.unary .fst (.var 1)) ∧
      (Term.unary .fst (.var 1) : Recipe 3).nodeCount < 3 := by
  refine ⟨⟨trivial, ?_⟩, by decide⟩
  intro r _ he
  exact ciphertext_recipe_size_ge_two σ _ _ _ (handles_not_ciphertext _ _ _)
    (he.symm.trans first_selector_control.1)

/-- The atom-exclusion premise is also necessary if a frame publishes the target itself. -/
theorem published_ciphertext_minimum :
    let τ : Fin 1 → Ground := fun _ => target
    MinimalRecipe ns.nonceNames τ (.var 0) ∧
      EqE ((Term.var 0).subst τ) target ∧
      (Term.var (V := Fin 1) 0).nodeCount < 2 := by
  exact ⟨MinimalRecipe.of_nodeCount_one trivial rfl, .refl _, by decide⟩

/-- The representation counterexample occurs in the actual fresh, accepting frame. -/
theorem fresh_accepted_context : ns.Fresh ∧
    Accepted 1 (publicKey ns) [] (ballot ns 0 0) :=
  ⟨HistoricalFrameSPOT.fixture_names_fresh, honest_empty_board_accepts ns 0 0⟩

end ExplainableCrypto.Helios.Symbolic.HistoricalSelectorSPOT
