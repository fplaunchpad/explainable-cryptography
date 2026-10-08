import ExplainableCrypto.Helios.Symbolic.SourceCaptureAlgebra

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Hide the old exported coordinate and retain a fresh public alias to it. -/
def captureCopy (f : Extended (Option V)) : Extended (Option V) :=
  .newVar (.par (f.rename (Option.map some)) (.active (some none) (.var none)))

private theorem copy_active (m : Term (Option V)) :
    Structural (captureCopy (.active none m)) (.active none m) := by
  let t := m.subst (fun v => .var (Option.map some v))
  have h₁ : Structural (.par (.active none t) (.active (some none) (.var none)))
      (.par (.active none t) (.active (some none) t)) := by
    simpa only [Term.subst,replaceVar,ite_true] using
      Structural.substActive none (some none) t (.var none) (by simp)
  have h₂ : Structural (.par (.active none (.var (some none))) (.active (some none) t))
      (.par (.active none t) (.active (some none) t)) := by
    have hs := Structural.substActive (some none) none t (.var (some none)) (by simp)
    simp only [Term.subst,replaceVar,ite_true] at hs
    exact (Structural.comm _ _).trans (hs.trans (Structural.comm _ _))
  have he : t.subst (inputSubst (.var none)) = m := by
    simp only [t,Term.subst_subst]
    conv_rhs => rw [← Term.subst_var m]
    congr 1
    funext v
    cases v <;> rfl
  have hi : Instantiates (inputSubst (.var none)) (.active (some none) t) (.active none m) := by
    simpa only [he] using Instantiates.active (inputSubst (.var none)) (some none) none t rfl
  exact (Structural.newVar (h₁.trans h₂.symm)).trans
    (Structural.let_normalize (.var none) (by simp [Exports]) hi)

private theorem redirect_context (g : Extended (Option V)) (hg : ¬ g.Exports none) :
    (g.rename some).substFree (some none) (.var none) = g.rename (Option.map some) := by
  have hn : ¬ (g.rename some).Exports (some none) :=
    fun h => hg ((rename_exports g some (Option.some_injective _) none).mp h)
  have h := (instantiates_rename g some).comp
    (instantiates_substFree (g.rename some) (some none) (.var none) hn)
  have he : (fun v : Option V => (Term.var (some v)).subst (replaceVar (some none) (.var none))) =
      (fun v => .var (Option.map some v)) := by
    funext v
    cases v <;> simp [Term.subst,replaceVar]
  rw [he] at h
  exact h.unique (instantiates_rename g (Option.map some))

private theorem copy_par (f g : Extended (Option V)) (hg : ¬ g.Exports none) :
    Structural (captureCopy (.par f g)) (.par (captureCopy f) g) := by
  let p : Extended (Option (Option V)) := .active (some none) (.var none)
  have hn : ¬ (g.rename some).Exports (some none) :=
    fun h => hg ((rename_exports g some (Option.some_injective _) none).mp h)
  have hs : Structural (.par p (g.rename (Option.map some))) (.par p (g.rename some)) := by
    rw [← redirect_context g hg]
    exact (Structural.substExtended (some none) (.var none) (g.rename some) hn).symm
  have rearrange (a b c : Extended (Option (Option V))) :
      Structural (.par (.par a b) c) (.par (.par a c) b) :=
    (Structural.assoc _ _ _).trans ((Structural.parRight _ (Structural.comm _ _)).trans
      (Structural.assoc _ _ _).symm)
  have h := (rearrange (f.rename (Option.map some)) (g.rename (Option.map some)) p).trans
    ((Structural.assoc _ _ _).trans ((Structural.parRight _ hs).trans (Structural.assoc _ _ _).symm))
  exact (Structural.newVar h).trans
    ((Structural.newVar (Structural.comm _ _)).trans
      ((Structural.newPar g _).symm.trans (Structural.comm _ _)))

private theorem copy_scope (a : Extended (Option (Option V))) :
    BinderStructural (captureCopy (.newVar a))
      (.newVar ((captureCopy (a.rename swapBinders)).rename swapBinders)) := by
  let t := a.rename (Option.map (Option.map some))
  let p : Extended (Option (Option V)) := .active (some none) (.var none)
  have h : Structural (captureCopy (.newVar a))
      (.newVar (.newVar (.par t (p.rename some)))) :=
    Structural.newVar ((Structural.comm _ _).trans
      ((Structural.newPar p t).trans (Structural.newVar (Structural.comm _ _))))
  have he : (Extended.par t (p.rename some)).rename swapBinders =
      .par (((a.rename swapBinders).rename (Option.map some)).rename (Option.map swapBinders))
        (.active (some (some none)) (.var none)) := by
    simp only [t,p,rename,rename_comp,Term.subst,swapBinders]
    congr 2
    funext v
    cases v with
    | none => rfl
    | some v => cases v <;> rfl
  exact h.binderStructural.trans (by
    have hs := BinderStructural.varComm (Extended.par t (p.rename some))
    rw [he] at hs
    exact hs)

private def frameSize : {V : Type} → Extended V → Nat
  | _, .plain _ => 1
  | _, .active _ _ => 1
  | _, .par a b => frameSize a + frameSize b + 1
  | _, .newVar a => frameSize a + 1

private theorem frameSize_rename (a : Extended V) {W : Type} (f : V → W) :
    frameSize (a.rename f) = frameSize a := by
  induction a generalizing W with
  | plain | active => rfl
  | par a b ih ij => simp only [rename,frameSize,ih,ij]
  | newVar a ih => simp only [rename,frameSize,ih]

/-- Copying the selected public provider through a fresh local alias preserves
its complete source frame, even when the provider payload depends on itself.
The only premises are the original uniqueness and exported-domain predicates. -/
theorem captureCopy_structural {V : Type} (f : Extended (Option V)) (hu : f.UniqueDefinitions)
    (hx : f.Exports none) : BinderStructural (captureCopy f) f := by
  cases hf : f with
  | plain p => rw [hf] at hx; exact hx.elim
  | active x m =>
    rw [hf] at hx
    change none = x at hx
    subst x
    exact (copy_active m).binderStructural
  | par a b =>
    rw [hf] at hu hx
    rcases hx with hx | hx
    · have hn : ¬ b.Exports none := fun hb => hu.2.2 none ⟨hx,hb⟩
      exact (copy_par a b hn).binderStructural.trans
        ((captureCopy_structural a hu.1 hx).parLeft b)
    · have hs : Structural (captureCopy (.par a b)) (captureCopy (.par b a)) :=
        Structural.newVar (Structural.parLeft _
          ((Structural.comm a b).rename (Option.map some) (Option.map_injective (Option.some_injective _))))
      have hn : ¬ a.Exports none := fun ha => hu.2.2 none ⟨ha,hx⟩
      exact hs.binderStructural.trans ((copy_par b a hn).binderStructural.trans
        (((captureCopy_structural b hu.2.1 hx).parLeft a).trans (Structural.comm b a).binderStructural))
  | newVar a =>
    rw [hf] at hu hx
    have hu' := (uniqueDefinitions_rename_iff a swapBinders swapBinders_involutive.injective).mpr hu.1
    have hx' : (a.rename swapBinders).Exports none :=
      (rename_exports a swapBinders swapBinders_involutive.injective (some none)).mpr hx
    have ih := captureCopy_structural (V := Option V) (a.rename (@swapBinders V)) hu' hx'
    have hr := (ih.named.rename swapBinders swapBinders_involutive.injective).binder_of_embeds
    have he : (a.rename swapBinders).rename swapBinders = a := by
      rw [rename_comp]
      have he : (@swapBinders V) ∘ swapBinders = id := funext swapBinders_involutive
      rw [he,rename_id]
    rw [he] at hr
    exact (copy_scope a).trans (BinderStructural.newVar hr)
termination_by frameSize f
decreasing_by all_goals (simp_all only [frameSize,frameSize_rename]; omega)

/-- The actual capture equality splits off the fresh ground provider while the
old frame is recovered by hiding precisely the old output coordinate. -/
theorem CapturedEq.ground_reclose {f : Extended (Option V)} {m : Ground}
    (h : CapturedEq f (.var none) (groundTerm m))
    (hu : f.UniqueDefinitions) (hx : f.Exports none) :
    BinderStructural f (.par ((Extended.newVar f).rename some) (.active none (groundTerm m))) := by
  have hf : (f.rename some).rename swapBinders = f.rename (Option.map some) := by
    rw [rename_comp]
    congr 1
    funext v
    cases v <;> rfl
  have hc := Structural.newVar (h.rename swapBinders swapBinders_involutive.injective)
  change Structural
    (.newVar ((captureFrame f (.var none)).rename swapBinders))
    (.newVar ((captureFrame f (groundTerm m)).rename swapBinders)) at hc
  simp only [captureFrame,rename,hf,shiftTerm,Term.subst,groundTerm_subst,swapBinders] at hc
  have he : Structural
      (.newVar (.par (f.rename (Option.map some)) (.active (some none) (groundTerm m))))
      (.par ((Extended.newVar f).rename some) (.active none (groundTerm m))) := by
    have hn := Structural.newPar (.active none (groundTerm m)) (f.rename (Option.map some))
    simp only [rename,groundTerm_subst] at hn
    exact (Structural.newVar (Structural.comm _ _)).trans
      (hn.symm.trans (Structural.comm _ _))
  exact (captureCopy_structural f hu hx).symm.trans (hc.binderStructural.trans he.binderStructural)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
