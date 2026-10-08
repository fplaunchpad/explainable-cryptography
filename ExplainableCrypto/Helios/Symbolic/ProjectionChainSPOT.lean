import ExplainableCrypto.Helios.Symbolic.HistoricalProjectionChains
import ExplainableCrypto.Helios.Symbolic.HistoricalSelectorSPOT

namespace ExplainableCrypto.Helios.Symbolic.ProjectionChainSPOT
open Historical

abbrev ns := HistoricalFrameSPOT.names
abbrev σ : Fin 3 → Ground := (frame ns false 0 1).value
abbrev key : Ground := .unary .pk (.name 10)
abbrev c₀ : Ground := .ternary .penc key (.name 20) (.const .one)
abbrev c₁ : Ground := .ternary .penc key (.name 21) (.const .zero)
abbrev p₀ : Ground := .spk key (.name 20) (.const .one) c₀
abbrev p₁ : Ground := .spk key (.name 21) (.const .zero) c₁
abbrev agg : Ground := .spk key (.binary .compose (.name 20) (.name 21))
  (.binary .add (.const .one) (.const .zero)) (.binary .mul c₀ c₁)
abbrev tailExpected : Ground := .binary .pair p₀ (.binary .pair p₁ (.binary .pair agg (.const .bottom)))
abbrev tailRecipe : Recipe 3 := (Term.var 1).drop 2
abbrev secondRecipe : Recipe 3 := (Term.var 1).project 1

/-- Two snd operations reach the independently written three-proof tail. -/
theorem tail_reaches_fixed : ProjectionChain 1 tailRecipe ∧
    ReducesModulo (tailRecipe.subst σ) tailExpected :=
  ⟨.drop 1 2, tuple_drop_reduces (ballotFields ns 0 0) 2 (by decide)⟩

theorem pair_tail_origin :
    ∃ k, k < 5 ∧ tailRecipe = (Term.var (V := Fin 3) 1).drop k :=
  voter_projection_pair_origin ns false 0 1 0 tail_reaches_fixed.1 tail_reaches_fixed.2.sound

theorem tail_is_not_ciphertext (k r m : Ground) :
    ¬ EqE (tailRecipe.subst σ) (.ternary .penc k r m) := by
  intro h
  exact penc_not_eqE_passive_binary .pair (Or.inl rfl) _ _ _ _ _
    (tail_reaches_fixed.2.sound.symm.trans h).symm

/-- The proof-bearing tail really has a reducible aggregate field. -/
theorem tail_has_actual_field_step :
    ModuloStep tailExpected
      (.binary .pair p₀ (.binary .pair p₁ (.binary .pair
        (.spk key (.binary .compose (.name 20) (.name 21))
          (.binary .add (.const .one) (.const .zero))
          (.ternary .penc key (.binary .compose (.name 20) (.name 21))
            (.binary .add (.const .one) (.const .zero)))) (.const .bottom)))) :=
  (RootStep.homomorphic key (.name 20) (.name 21) (.const .one) (.const .zero)).to_modulo.context
    (.binaryRight .pair p₀ (.binaryRight .pair p₁ (.binaryLeft .pair
      (.spkFourth key (.binary .compose (.name 20) (.name 21))
        (.binary .add (.const .one) (.const .zero)) .hole) (.const .bottom))))

/-- The general origin theorem retains the actual second-field recipe and value. -/
theorem second_ciphertext_origin :
    MinimalRecipe ns.nonceNames σ secondRecipe ∧ ProjectionChain 1 secondRecipe ∧
    ∃ j : Fin 2, secondRecipe = (Term.var (V := Fin 3) 1).project j.val ∧
      EqE (ciphertext ns 0 0 j) c₁ :=
  ⟨HistoricalSelectorSPOT.second_minimal _, .project 1 1,
    voter_projection_ciphertext_origin ns false 0 1 0 (.project 1 1)
      HistoricalSelectorSPOT.second_evaluation⟩

theorem second_ciphertext_supplies_product :
    CiphertextProduct σ key secondRecipe (.const .zero) (.name 21) :=
  honest_projection_product ns false 0 1 0 1

/-- The full all-handle theorem constructs the certificate, rather than assuming it. -/
theorem chain_class_supplies_certificate :
    ∃ i : Fin 2, ∃ j : Fin 2, (1 : Fin 3) = i.succ ∧
      secondRecipe = (Term.var i.succ).project j.val ∧
      CiphertextProduct σ (publicKey ns) secondRecipe
        (.const (if j = choice false (0 : Fin 2) 1 i then .one else .zero)) (.name (ns.nonce i j)) :=
  projection_chain_product ns false 0 1 1 (.project 1 1) HistoricalSelectorSPOT.second_evaluation

theorem swapped_ciphertext_origin :
    EqE ((frame ns true 0 1).eval secondRecipe)
      (.ternary .penc key (.name 21) (.const .one)) ∧
    ∃ j : Fin 2, secondRecipe = (Term.var (V := Fin 3) 1).project j.val ∧
      EqE (ciphertext ns 0 1 j) (.ternary .penc key (.name 21) (.const .one)) := by
  have hv : EqE ((frame ns true 0 1).eval secondRecipe)
      (.ternary .penc key (.name 21) (.const .one)) := ballot_project_ciphertext ns 0 1 1
  exact ⟨hv, voter_projection_ciphertext_origin ns true 0 1 0 (.project 1 1) hv⟩

abbrev proofRecipe : Recipe 3 := (Term.var 1).project 2
abbrev aggregateRecipe : Recipe 3 := (Term.var 1).project 4

theorem proof_positions_reach_fixed : EqE (proofRecipe.subst σ) p₀ ∧
    EqE (aggregateRecipe.subst σ) agg :=
  ⟨ballot_project_proof ns 0 0 0, ballot_project_aggregate ns 0 0⟩

theorem proof_positions_not_ciphertext (k r m : Ground) :
    ¬ EqE (proofRecipe.subst σ) (.ternary .penc k r m) ∧
    ¬ EqE (aggregateRecipe.subst σ) (.ternary .penc k r m) :=
  ⟨fun h => penc_not_eqE_spk _ _ _ _ _ _ _ (proof_positions_reach_fixed.1.symm.trans h).symm,
    fun h => penc_not_eqE_spk _ _ _ _ _ _ _ (proof_positions_reach_fixed.2.symm.trans h).symm⟩

theorem proof_chain_origin :
    (∃ j : Fin 2, proofRecipe = (Term.var (V := Fin 3) 1).project (2 + j.val) ∧
      EqE (componentProof ns 0 0 j) p₀) ∨
    (proofRecipe = (Term.var (V := Fin 3) 1).project 4 ∧ EqE (aggregateProof ns 0 0) p₀) :=
  voter_projection_proof_origin ns false 0 1 0 (.project 1 2) proof_positions_reach_fixed.1

theorem key_chain_excluded (k r m : Ground) :
    ¬ EqE (((Term.var (V := Fin 3) 0).project 3).subst σ) (.ternary .penc k r m) :=
  key_projection_chain_not_ciphertext ns false 0 1 (.project 0 3) k r m

/-- The first out-of-range field is fst(bottom), preserving the source guard counterexample. -/
theorem past_end_is_stuck :
    EqE (((Term.var (V := Fin 3) 1).project 5).subst σ) (.unary .fst (.const .bottom)) ∧
    ¬ EqE (((Term.var (V := Fin 3) 1).project 5).subst σ) (.const .bottom) ∧
    ¬ EqE (((Term.var (V := Fin 3) 1).project 5).subst σ) c₀ := by
  have he : EqE (((Term.var (V := Fin 3) 1).project 5).subst σ)
      (.unary .fst (.const .bottom)) := next_projection_tuple (ballotFields ns 0 0)
  exact ⟨he, fun h => fst_bottom_not_bottom (he.symm.trans h),
    fun h => projection_not_eqE_penc_of_irreducible (constant_irreducible .bottom)
      (by decide) .fst (he.symm.trans h)⟩

abbrev hiddenPair : Ground := .unary .fst (.binary .pair (.binary .pair (.name 0) (.name 1)) (.const .bottom))
abbrev badSubstitution : Fin 1 → Ground := fun _ => Term.tuple [hiddenPair]
abbrev badRecipe : Recipe 1 := .unary .fst (.var 0)

/-- A syntactically non-pair field can reduce to a pair: the premise must be about E-values. -/
theorem nonpair_field_premise_required :
    ProjectionChain 0 badRecipe ∧
    (∀ x y, hiddenPair ≠ .binary .pair x y) ∧
    ReducesModulo (badRecipe.subst badSubstitution) (.binary .pair (.name 0) (.name 1)) ∧
    ¬ (∃ k, badRecipe = (Term.var (V := Fin 1) 0).drop k) := by
  refine ⟨.project 0 0, ?_, ?_, ?_⟩
  · intro x y h
    cases h
  · exact (ReducesModulo.single (RootStep.fst hiddenPair (.const .bottom)).to_modulo).trans
      (.single (RootStep.fst (.binary .pair (.name 0) (.name 1)) (.const .bottom)).to_modulo)
  · rintro ⟨k, he⟩
    cases k with
    | zero => cases he
    | succ k => rw [Term.drop_succ_outer] at he; cases he

/-- The literal pair-field gate counterexample is also retained as a checked path. -/
theorem literal_pair_field_counterexample :
    ReducesModulo ((Term.tuple [Term.binary (V := Nat) .pair (.name 0) (.name 1)]).project 0)
      (.binary .pair (.name 0) (.name 1)) :=
  .single (RootStep.fst (.binary .pair (.name 0) (.name 1)) (.const .bottom)).to_modulo

end ExplainableCrypto.Helios.Symbolic.ProjectionChainSPOT
