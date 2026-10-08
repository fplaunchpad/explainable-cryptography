import ExplainableCrypto.Helios.Symbolic.SourceFrameAlgebraQuotient
import ExplainableCrypto.Helios.Symbolic.SourceFrameCompatibilitySPOT
import ExplainableCrypto.Helios.Symbolic.SourceBoundRigiditySPOT

namespace ExplainableCrypto.Helios.Symbolic.SourceFrameAlgebraSPOT
open Historical General Source

/-- The algebra control satisfies a real destructor equation, rather than
interpreting the full equation model as uninterpreted syntax. -/
theorem full_equation_is_respected :
    FrameAlgebra.fullGround.eval (V := Fin 0) Fin.elim0
      (.unary .fst (.binary .pair (.name 40) (.name 41))) =
    FrameAlgebra.fullGround.eval (V := Fin 0) Fin.elim0 (.name 40) :=
  FrameAlgebra.fullGround.eval_eq _ (EqE.equation (.fst _ _))

theorem concrete_model_is_not_trivial :
    (Term.name 40 : Ground).fullClass ≠ (Term.name 41 : Ground).fullClass :=
  FrameAlgebra.fullGround_names_distinct (by decide)

/-- Alias existence and uniqueness follow from the actual structural rule in
every model; they are not independent premises of the new preservation theorem. -/
theorem local_alias_is_inhabited_and_rigid (M : FrameAlgebra) {V : Type}
    (env : V → M.Value) (r : Term V) :
    M.Satisfies (.newVar (.active none (shiftTerm r))) env ∧
      M.Rigid (.newVar (.active none (shiftTerm r))) env :=
  ⟨(M.structural_satisfies (.alias r) env).mpr True.intro,
    (M.structural_rigid (.alias r) env).mpr True.intro⟩

theorem dependent_binder_exchange_retains_both_constraints (M : FrameAlgebra) :
    (M.Satisfies SourceBoundRigiditySPOT.dependentLocals Empty.elim ↔
      M.Satisfies (.newVar (.newVar
        (SourceBoundRigiditySPOT.dependentBody.rename Extended.swapBinders))) Empty.elim) ∧
    (M.Rigid SourceBoundRigiditySPOT.dependentLocals Empty.elim ↔
      M.Rigid (.newVar (.newVar
        (SourceBoundRigiditySPOT.dependentBody.rename Extended.swapBinders))) Empty.elim) :=
  ⟨M.binder_satisfies (.varComm _) _,M.binder_rigid (.varComm _) _⟩

abbrev openedCapture : Extended (Option (Fin 0)) :=
  .par (.active none (.name 100)) (.plain .nil)

private theorem capture_opening :
    Named.Opens SourceFrameCompatibilitySPOT.latentPrivateCapture NameAssignment.literal
      [.base 100] openedCapture :=
  .newName (.base 40) 100 (.embed _ _) (by decide)

/-- Actual source provenance derives the fresh-value equality for any full-E
algebra, even when its carrier has values beyond ordinary ground E-classes. -/
theorem actual_output_derives_value_uniqueness (M : FrameAlgebra) (m n : M.Value)
    (hm : M.Satisfies openedCapture (M.extend Fin.elim0 m))
    (hn : M.Satisfies openedCapture (M.extend Fin.elim0 n)) : m = n :=
  SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output.opened_value_unique
    SourceFrameCompatibilitySPOT.latent_private_name_can_be_retained_in_old_policy
    capture_opening M Fin.elim0 m n hm hn

theorem actual_opening_has_the_fresh_value :
    FrameAlgebra.fullGround.Satisfies openedCapture
      (FrameAlgebra.fullGround.extend Fin.elim0 (Term.name 100 : Ground).fullClass) :=
  ⟨rfl,True.intro⟩

theorem actual_opening_rejects_the_old_spelling :
    ¬ FrameAlgebra.fullGround.Satisfies openedCapture
      (FrameAlgebra.fullGround.extend Fin.elim0 (Term.name 40 : Ground).fullClass) :=
  fun h => FrameAlgebra.fullGround_names_distinct (by decide : (40 : Nat) ≠ 100) h.1

/-- The ground witness is extracted from the original presentation/reclosure;
the caller does not supply a value or an algebraic realization certificate. -/
theorem actual_output_derives_its_ground_witness :
    ∃ m : Ground, EqE m (.name 100) ∧
      ∀ (M : FrameAlgebra) (v : M.Value),
        M.Satisfies openedCapture (M.extend Fin.elim0 v) → v = M.groundValue m := by
  obtain ⟨_,m,hm,hall⟩ :=
    SourceFrameCompatibilitySPOT.latent_private_name_has_actual_output.opened_algebra_values
      SourceFrameCompatibilitySPOT.latent_private_name_can_be_retained_in_old_policy capture_opening
  exact ⟨m,hm.1,fun M v hv => (hall M Fin.elim0 v hv).2⟩

abbrev zeroFrame : Frame ∅ 1 := ⟨fun _ => .const .zero⟩
abbrev oneOutput : ScopedState ∅ 1 := ⟨zeroFrame,.output 0 (.const .one) .nil⟩
abbrev oneCapture : Extended (Option (Fin 1)) :=
  .par ((Extended.activeFrame zeroFrame).rename some)
    (Extended.capture (Extended.groundTerm (.const .one)) (Extended.groundAgent .nil))

private theorem one_publication :
    Named.BoundOutput (Named.restrictedState ∅ oneOutput) 0 (.embed oneCapture) := by
  simpa only [Named.restrictedState,Named.restrictionNames,Finset.toList_empty,List.map_nil,
    List.append_nil,Named.restrictNames,List.foldr_nil] using
    Named.BoundOutput.embed (Extended.frame_output_derivable zeroFrame 0 (.const .one) .nil)

private theorem one_opening : Named.Opens (.embed oneCapture) NameAssignment.literal [] oneCapture := by
  simpa only [show NameAssignment.literal.base = id from rfl,
    show NameAssignment.literal.channel = id from rfl,Extended.mapNames_id] using
    Named.Opens.embed oneCapture NameAssignment.literal

/-- Full old and fresh values are derived together. The old public zero is not
replaced by the newly published one. -/
theorem old_zero_and_new_one_are_both_retained (M : FrameAlgebra)
    (env : Fin 1 → M.Value) (v : M.Value)
    (hv : M.Satisfies oneCapture (M.extend env v)) :
    env 0 = M.groundValue (.const .zero) ∧ v = M.groundValue (.const .one) := by
  obtain ⟨_,m,hm,hall⟩ := one_publication.opened_algebra_values
    (Named.restrictedState_represents oneOutput) one_opening
  have he : EqE m (.const .one) := hm.2.1
  obtain ⟨hold,hnew⟩ := hall M env v hv
  exact ⟨hold 0,hnew.trans (M.eval_eq Empty.elim he)⟩

theorem distinct_old_and_fresh_values_have_a_model :
    FrameAlgebra.fullGround.Satisfies oneCapture
      (FrameAlgebra.fullGround.extend (fun _ => (Term.const .zero : Ground).fullClass)
        (Term.const .one : Ground).fullClass) ∧
    (Term.const .zero : Ground).fullClass ≠ (Term.const .one : Ground).fullClass :=
  ⟨⟨⟨rfl,True.intro⟩,⟨rfl,True.intro⟩⟩,
    fun h => zero_not_one ((fullClass_eq_iff _ _).mp h)⟩

/-- The same inhabited cycle remains non-rigid in a nontrivial equation model.
Universal model rigidity therefore does not silently admit the old shortcut. -/
theorem cyclic_local_still_fails_rigidity :
    ¬ FrameAlgebra.fullGround.Rigid
      (.newVar (.active none (.var none)) : Extended (Fin 0)) Fin.elim0 := by
  intro h
  have hm : FrameAlgebra.fullGround.Satisfies (.active none (.var none))
      (FrameAlgebra.fullGround.extend Fin.elim0 (Term.name 40 : Ground).fullClass) :=
    (FrameAlgebra.fullGround.eval_var _ none).symm
  have hn : FrameAlgebra.fullGround.Satisfies (.active none (.var none))
      (FrameAlgebra.fullGround.extend Fin.elim0 (Term.name 41 : Ground).fullClass) :=
    (FrameAlgebra.fullGround.eval_var _ none).symm
  exact concrete_model_is_not_trivial (h.1 _ _ hm hn)

end ExplainableCrypto.Helios.Symbolic.SourceFrameAlgebraSPOT
