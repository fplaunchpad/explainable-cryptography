import ExplainableCrypto.Helios.Symbolic.SourceFrameContextSubstitution
import ExplainableCrypto.Helios.Symbolic.SourceNamedFramePresentation

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {restricted : Finset Nat} {handles : Nat}

/-- The old public providers ground the entire fresh capture and continuation;
the fresh active domain stays None. No groundness assumption on the recipe is
needed, and the continuation may use both old and new handles. -/
theorem frame_recipe_capture_ground (φ : Frame restricted handles) (r : Recipe handles)
    (p : Agent (Option (Fin handles))) :
    Structural
      (.par ((activeFrame φ).rename some) (.par (.active none (shiftTerm r)) (.plain p)))
      (.par ((activeFrame φ).rename some)
        (.par (.active none (groundTerm (φ.eval r)))
          (.plain (groundAgent (p.subst (extendEnv φ.value (φ.eval r))))))) := by
  let σ : Fin handles → Term (Fin handles) := fun i => groundTerm (φ.value i)
  have hx : (shiftTerm r).subst (liftSubst σ) = groundTerm (φ.eval r) := by
    rw [shiftTerm_subst]
    change shiftTerm (r.subst (fun i => groundTerm (φ.value i))) = _
    rw [recipe_ground_eval]
    exact groundTerm_subst _ _
  have hi : Instantiates (liftSubst σ) (.par (.active none (shiftTerm r)) (.plain p))
      (.par (.active none (groundTerm (φ.eval r))) (.plain (p.subst (liftSubst σ)))) := by
    have hh := Instantiates.par (Instantiates.active (liftSubst σ) none none (shiftTerm r) rfl)
      (Instantiates.plain (liftSubst σ) p)
    simpa only [hx] using hh
  have hs := shiftedFrame_apply_instantiates φ (by intro i; simp only [Exports,Option.some_ne_none,or_self]; exact not_false) hi
  have ht := Structural.parRight ((activeFrame φ).rename some)
    (Structural.substPlain none (groundTerm (φ.eval r)) (p.subst (liftSubst σ)))
  have he : (p.subst (liftSubst σ)).subst (replaceVar none (groundTerm (φ.eval r))) =
      (groundAgent (p.subst (extendEnv φ.value (φ.eval r))) : Agent (Option (Fin handles))) := by
    simp only [groundAgent,Agent.subst_subst]
    congr 1
    funext v
    cases v with
    | none =>
      change replaceVar none (groundTerm (φ.eval r)) none = groundTerm (φ.eval r)
      simp [replaceVar]
    | some i =>
      change ((groundTerm (φ.value i) : Term (Fin handles)).subst (fun v => .var (some v))).subst
        (replaceVar none (groundTerm (φ.eval r))) = groundTerm (φ.value i)
      rw [groundTerm_subst,groundTerm_subst]
  rw [he] at ht
  exact hs.trans ht

/-- Canonical fresh-handle naming reconstructs the full extended public frame
and the complete evaluated continuation through original structural rules. -/
theorem frame_recipe_capture_normalize (φ : Frame restricted handles) (r : Recipe handles)
    (p : Agent (Option (Fin handles))) :
    Structural
      ((Extended.par ((activeFrame φ).rename some)
        (.par (.active none (shiftTerm r)) (.plain p))).rename outputHandle)
      (frameProcess (φ.extend (φ.eval r)) (p.subst (extendEnv φ.value (φ.eval r)))) := by
  have hs := (frame_recipe_capture_ground φ r p).rename outputHandle outputHandle.injective
  have ht := frame_output_capture φ (φ.eval r) (p.subst (extendEnv φ.value (φ.eval r)))
  simp only [capture,shiftTerm,groundTerm_rename,Agent.shift,groundAgent_subst] at ht
  exact hs.trans ht

/-- A raw recipe-valued output has its original bound-output derivation and a
full canonical target after the fresh public handle is named. -/
theorem frame_recipe_output (φ : Frame restricted handles) (c : Nat) (r : Recipe handles)
    (p : Agent (Fin handles)) :
    BoundOutput (.par (activeFrame φ) (.plain (.output c r p))) c
      (.par ((activeFrame φ).rename some) (capture r p)) ∧
    Structural ((Extended.par ((activeFrame φ).rename some) (capture r p)).rename outputHandle)
      (frameProcess (φ.extend (φ.eval r)) (p.subst φ.value)) := by
  refine ⟨.parRight _ (message_output c r p),?_⟩
  have hs := frame_recipe_capture_normalize φ r p.shift
  have he : p.shift.subst (extendEnv φ.value (φ.eval r)) = p.subst φ.value := by
    simp only [Agent.shift,Agent.subst_subst,Term.subst,extendEnv]
  simpa only [capture,he] using hs

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
variable {restricted hidden : Finset Nat} {handles : Nat}

/-- The same original name prefix encloses the full provider values, recipe
capture and evaluated continuation throughout reconstruction. -/
theorem restricted_recipe_capture_normalize (φ : Frame restricted handles) (r : Recipe handles)
    (p : Agent (Option (Fin handles))) :
    Structural
      ((restrictNames (restrictionNames hidden restricted)
        (.embed (.par ((Extended.activeFrame φ).rename some)
          (.par (.active none (shiftTerm r)) (.plain p))))).rename Extended.outputHandle)
      (restrictedState hidden ⟨φ.extend (φ.eval r),p.subst (extendEnv φ.value (φ.eval r))⟩) := by
  simpa only [restrictNames_rename,rename,restrictedState] using
    (Structural.embed (Extended.frame_recipe_capture_normalize φ r p)).restrictNames
      (restrictionNames hidden restricted)

/-- A complete actual frame-presentation witness, rather than an interpretation
or reclosed old-frame certificate, for this recipe-valued capture class. -/
theorem restricted_recipe_capture_represents (φ : Frame restricted handles) (r : Recipe handles)
    (p : Agent (Option (Fin handles))) :
    (((restrictNames (restrictionNames hidden restricted)
      (.embed (.par ((Extended.activeFrame φ).rename some)
        (.par (.active none (shiftTerm r)) (.plain p))))).rename Extended.outputHandle)).RepresentsFrame
      hidden (φ.extend (φ.eval r)) :=
  (restrictedState_represents _).structural (restricted_recipe_capture_normalize φ r p).symm

/-- A non-ground recipe output under the actual private-name policy has an
original bound action and a complete reconstructed target. Only its channel
must be public; publishing the recipe value is an action, not a secrecy claim. -/
theorem restricted_recipe_output (φ : Frame restricted handles) (c : Nat) (hc : c ∉ hidden)
    (r : Recipe handles) (p : Agent (Fin handles)) :
    ∃ b : Named (Option (Fin handles)),
      BoundOutput (restrictNames (restrictionNames hidden restricted)
        (.embed (.par (Extended.activeFrame φ) (.plain (.output c r p))))) c b ∧
      Structural (b.rename Extended.outputHandle)
        (restrictedState hidden ⟨φ.extend (φ.eval r),p.subst φ.value⟩) := by
  obtain ⟨ho,hs⟩ := Extended.frame_recipe_output φ c r p
  refine ⟨_,(BoundOutput.embed ho).restrictNames _ ((output_restriction_fresh_iff c).mpr hc),?_⟩
  simpa only [restrictNames_rename,rename,restrictedState] using
    (Structural.embed hs).restrictNames (restrictionNames hidden restricted)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Named
