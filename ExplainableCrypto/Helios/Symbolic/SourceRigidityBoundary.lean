import ExplainableCrypto.Helios.Symbolic.SourceRigidityPreservation
import ExplainableCrypto.Helios.Symbolic.SourceJointOpening

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type} {restricted : Finset Nat} {handles : Nat}

/-- Existential interpretation forgets an unconstrained local value. This
holds for every outer variable environment and complete plain-body class. -/
theorem unconstrained_local_sameRealizations :
    (Extended.newVar (.active none (.var none)) : Extended V).SameRealizations (.plain .nil) := by
  intro env p
  constructor
  · rintro ⟨_,_,hp⟩
    exact hp
  · intro hp
    exact ⟨.name 40,.refl _,hp⟩

/-- Two distinct names witness failure of local uniqueness independently of
all outer variables and frame contents. -/
theorem unconstrained_local_not_rigid (env : V → Ground) :
    ¬ (Extended.newVar (.active none (.var none)) : Extended V).Rigid env := by
  intro h
  have he := h.1 (.name 40) (.name 41) (EqE.refl _) (EqE.refl _)
  have hn := (EqE.name_iff 40 41).mp he
  cases hn

/-- The same loss persists beside any complete public frame and any body. -/
theorem frame_with_unconstrained_local_sameRealizations (φ : Frame restricted handles) (p : Agent Empty) :
    (Extended.par (frameProcess φ p) (.newVar (.active none (.var none)))).SameRealizations
      (frameProcess φ p) :=
  ((SameRealizations.refl _).par unconstrained_local_sameRealizations).trans (Structural.zero _).sameRealizations

theorem frame_with_unconstrained_local_wellFormed (φ : Frame restricted handles) (p : Agent Empty) :
    (Extended.par (frameProcess φ p) (.newVar (.active none (.var none)))).WellFormed := by
  refine ⟨⟨(frameProcess_wellFormed φ p).1,⟨True.intro,rfl⟩,?_⟩,?_⟩
  · intro v h
    exact Option.some_ne_none v h.2
  · exact closed_of_all_exports _ (fun v => Or.inl (frameProcess_all_exports φ p v))

/-- Nonvacuity does not repair the missing invariant: even beside a real
complete frame, the unconstrained local blocks Extended normalization. -/
theorem frame_with_unconstrained_local_not_structural (φ : Frame restricted handles) (p : Agent Empty) :
    ¬ Structural (.par (frameProcess φ p) (.newVar (.active none (.var none)))) (frameProcess φ p) := by
  intro h
  have hr := h.rigid_of_frame_target φ p φ.value
  have hs : (frameProcess φ p).Satisfies φ.value := by
    change (activeFrame φ).Satisfies φ.value ∧ True
    exact ⟨(activeFrame_satisfies_iff φ φ.value).mpr (fun _ => .refl _),True.intro⟩
  exact unconstrained_local_not_rigid φ.value (hr hs ⟨.name 40,.refl _⟩).2

/-- Embedded joint openings also identify the padded process with its complete
frame/body partner. The non-Structural conclusion above is Extended only. -/
theorem frame_with_unconstrained_local_joint (φ : Frame restricted handles) (p : Agent Empty) :
    Named.JointOpening (.embed (.par (frameProcess φ p) (.newVar (.active none (.var none)))))
      (.embed (frameProcess φ p)) := by
  have he := frame_with_unconstrained_local_sameRealizations φ p
  exact Named.JointOpening.embed he ((he _ _).mpr (frameProcess_realizes φ p))

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
