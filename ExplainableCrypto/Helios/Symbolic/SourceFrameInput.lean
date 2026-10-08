import ExplainableCrypto.Helios.Symbolic.SourceFrameSubstitution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- In substitutes the literal recipe first; active-frame evaluation then
agrees with receiving its ground value. The newer input binders remain local. -/
theorem input_frame_evaluation (φ : Frame restricted handles) (body : Agent (Option Empty)) (r : Recipe handles) :
    (((body.subst (liftSubst (Empty.elim : Empty → Term (Fin handles)))).bind r).subst
      (fun i => groundTerm (φ.value i))) = (groundAgent (body.bind (φ.eval r)) : Agent (Fin handles)) := by
  simp only [Agent.bind,Agent.subst_subst,groundAgent]
  congr 1
  funext v
  cases v with
  | none => exact recipe_ground_eval φ r
  | some v => exact v.elim

/-- Source In uses the original recipe as its label. The parallel active frame
then evaluates the received continuation via source Subst, retaining a full
unrelated ground context. Acceptance is not an input premise. -/
theorem frame_input_in_context (φ : Frame restricted handles) (c : Nat)
    (body : Agent (Option Empty)) (context : Agent Empty) (r : Recipe handles) :
    FreeStep (frameProcess φ (.par (.input c body) context)) (.input c r)
      (frameProcess φ (.par (body.bind (φ.eval r)) context)) := by
  let raw : Agent (Fin handles) := .par
    ((body.subst (liftSubst (Empty.elim : Empty → Term (Fin handles)))).bind r) (groundAgent context)
  have hv : FreeStep (.plain (groundAgent (.par (.input c body) context))) (.input c r) (.plain raw) :=
    .congr (.plainPar _ _) (.parLeft (.plain (groundAgent context)) (.input c r _)) (Structural.plainPar _ _).symm
  have hs := activeFrame_apply φ raw
  have he : raw.subst (fun i => groundTerm (φ.value i)) =
      (groundAgent (.par (body.bind (φ.eval r)) context) : Agent (Fin handles)) := by
    simp only [raw,Agent.subst,input_frame_evaluation,groundAgent_subst]
    rfl
  rw [he] at hs
  exact .congr (.refl _) (.parRight (activeFrame φ) hv) hs

/-- Every evaluated visible input beside its actual active frame has the same
literal-recipe source label and complete target, including arbitrary ParEq. -/
theorem frame_visible_input_derivable (φ : Frame restricted handles) (r : Recipe handles)
    {p q : Agent Empty} {c : Nat} (h : Agent.Visible p (.input c (φ.eval r)) q) :
    FreeStep (frameProcess φ p) (.input c r) (frameProcess φ q) := by
  obtain ⟨body,context,hp,hq⟩ := h.input_context
  have hp' : Agent.ParEq p (.par (.input c body) context) :=
    (Agent.parEq_iff_threads _ _).mpr (by simpa only [Agent.threads_par] using hp)
  have hq' : Agent.ParEq (.par (body.bind (φ.eval r)) context) q :=
    (Agent.parEq_iff_threads _ _).mpr (by simpa only [Agent.threads_par] using hq.symm)
  exact .congr (.parRight _ (parEq_derivable (hp'.subst Empty.elim)))
    (frame_input_in_context φ c body context r) (.parRight _ (parEq_derivable (hq'.subst Empty.elim)))

/-- All evaluated public recipe inputs are derived from In and the explicit
active bindings. The source label remains the recipe, not its ground value.
Name-scope filtering and the full operational converse are separate obligations. -/
theorem scoped_input_derivable (hidden : Finset Nat) (p q : ScopedState restricted handles)
    (c : Nat) (r : Recipe handles) (h : ScopedStep hidden restricted p (.input c r) q) :
    FreeStep (frameProcess p.frame p.body) (.input c r) (frameProcess q.frame q.body) := by
  obtain ⟨_,_,he,hv⟩ := (scoped_input_iff p q c r).mp h
  rw [← he]
  exact frame_visible_input_derivable p.frame r hv
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
