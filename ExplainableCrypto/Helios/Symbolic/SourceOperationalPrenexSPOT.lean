import ExplainableCrypto.Helios.Symbolic.SourceFreshOperationalPrenex
import ExplainableCrypto.Helios.Symbolic.SourceNameInterpretationSPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceOperationalPrenexSPOT
open Historical General Source Extended

abbrev φ := SourceAtomicOutputSPOT.oldFrame
abbrev sender : Agent Empty := .output 8 (.name 41) .nil
abbrev receiver : Agent Empty := .input 8 (.output 9 (.var none) .nil)
abbrev afterComm : Agent Empty := .par .nil (.output 9 (.name 41) .nil)
abbrev beforeNamed : Named (Fin 1) :=
  .newName (.channel 8) (.embed (frameProcess φ (.par sender receiver)))
abbrev afterNamed : Named (Fin 1) :=
  .newName (.channel 8) (.embed (frameProcess φ afterComm))

private theorem private_step : Named.Reduction beforeNamed afterNamed := by
  apply Named.Reduction.newName
  apply Named.Reduction.embed
  apply Extended.Reduction.parRight
  exact tau_ground_derivable _ (Agent.Tau.of_core (.comm _ _ _ _))

/-- A private handshake factors to one genuine Extended reduction. -/
theorem private_internal_common_prefix :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural beforeNamed (Named.restrictNames ns (.embed a)) ∧
      Named.Structural afterNamed (Named.restrictNames ns (.embed b)) ∧ Extended.Reduction a b :=
  private_step.prenex

/-- Arbitrary requested avoidance does not delete or replace the actual step. -/
theorem private_internal_distinct_fresh :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural beforeNamed (Named.restrictNames ns (.embed a)) ∧
      Named.Structural afterNamed (Named.restrictNames ns (.embed b)) ∧ Extended.Reduction a b ∧
      ns.Nodup ∧ ∀ n ∈ ns, n ∉ ({.channel 8,.base 40,.base 41} : Finset SourceName) :=
  private_step.fresh_prenex _

/-- Reconstruction uses the same common prefix and source Struct paths. -/
theorem private_internal_reconstructed : Named.Reduction beforeNamed afterNamed :=
  (Named.reduction_iff_prenex beforeNamed afterNamed).mpr private_internal_common_prefix

abbrev alphaSource : Named (Fin 1) :=
  .newName (.base 40) (.embed (SourceInputAlphaBoundary.keyAndInput 40))
abbrev alphaTarget : Named (Fin 1) :=
  .newName (.base 41) (.embed (.par (.active 0 (.unary .pk (.name 41)))
    (.plain (.output 0 (.name 40) .nil))))

/-- The retained alpha-input boundary factors with its literal 40 unchanged,
and its new common prefix binds none of that exact label's names. -/
theorem alpha_input_exact_factorization :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural alphaSource (Named.restrictNames ns (.embed a)) ∧
      Named.Structural alphaTarget (Named.restrictNames ns (.embed b)) ∧
      Extended.FreeStep a (.input 0 (.name 40)) b ∧
      ∀ n ∈ ns, n ∉ (Extended.FreeLabel.input 0 (.name 40) : Extended.FreeLabel (Fin 1)).nameSupport :=
  SourceInputAlphaBoundary.old_literal_input_after_alpha.prenex

theorem alpha_input_cannot_bind_received_literal :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural alphaSource (Named.restrictNames ns (.embed a)) ∧
      Named.Structural alphaTarget (Named.restrictNames ns (.embed b)) ∧
      Extended.FreeStep a (.input 0 (.name 40)) b ∧ SourceName.base 40 ∉ ns := by
  obtain ⟨ns,a,b,ha,hb,hr,hn⟩ := alpha_input_exact_factorization
  exact ⟨ns,a,b,ha,hb,hr,fun hm => hn (.base 40) hm (by decide)⟩

theorem alpha_input_fresh_away_from_second_world :
    ∃ (ns : List SourceName) (a b : Extended (Fin 1)),
      Named.Structural alphaSource (Named.restrictNames ns (.embed a)) ∧
      Named.Structural alphaTarget (Named.restrictNames ns (.embed b)) ∧
      Extended.FreeStep a (.input 0 (.name 40)) b ∧ ns.Nodup ∧
      ∀ n ∈ ns, n ∉ ({.base 41,.channel 9} : Finset SourceName) ∪
        (Extended.FreeLabel.input 0 (.name 40) : Extended.FreeLabel (Fin 1)).nameSupport :=
  SourceInputAlphaBoundary.old_literal_input_after_alpha.fresh_prenex _

theorem alpha_input_reconstructed : Named.FreeStep alphaSource (.input 0 (.name 40)) alphaTarget :=
  (Named.freeStep_iff_prenex alphaSource alphaTarget _).mpr alpha_input_exact_factorization

abbrev proofRecipe : Recipe 1 := .spk (.var 0) (.name 41) (.const .zero)
  (.ternary .penc (.var 0) (.name 48) (.const .one))

/-- Fixed support includes a literal appearing only in the fourth proof field. -/
theorem fourth_field_in_label_support :
    SourceName.base 48 ∈ (FreeLabel.input 0 proofRecipe).nameSupport := by decide

theorem fourth_field_renaming_cannot_fix_label :
    (FreeLabel.input 0 proofRecipe).mapNames (Equiv.swap 48 50) id ≠ .input 0 proofRecipe := by
  simp [FreeLabel.mapNames,proofRecipe,Term.mapNames,Equiv.swap_apply_def]

theorem unrelated_name_permutation_fixes_complete_label :
    (FreeLabel.input 0 proofRecipe).mapNames (Equiv.swap 40 50) id = .input 0 proofRecipe := by
  simp [FreeLabel.mapNames,proofRecipe,Term.mapNames,Equiv.swap_apply_def]

/-- A private action remains blocked; factorization does not relax Scope. -/
theorem private_input_still_blocked (target : Named (Fin 1)) :
    ¬ Named.FreeStep beforeNamed (.input 8 proofRecipe) target := by
  intro h
  have hm := h.channel_mem
  exact (by decide : 8 ∉ beforeNamed.channels) hm

/-- An independently given factored source realization yields actual behavior;
the general theorem does not assume all representatives use the same env. -/
theorem interpreted_private_primitive :
    ∃ q, Agent.Tau (.par sender receiver) q ∧
      (frameProcess φ afterComm).Realizes φ.value q := by
  apply frameProcess_reduction_interpreted φ (.par sender receiver)
  apply Extended.Reduction.parRight
  exact tau_ground_derivable _ (Agent.Tau.of_core (.comm _ _ _ _))

end ExplainableCrypto.Helios.Symbolic.SourceOperationalPrenexSPOT
