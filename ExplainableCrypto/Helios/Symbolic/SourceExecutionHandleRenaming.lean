import ExplainableCrypto.Helios.Symbolic.SourceRigidExecution

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source
variable {V W : Type}

namespace Extended

/-- Existing execution reindexing needs action transport under handle bijections. -/
theorem Reduction.rename_equiv {a b : Extended V} (h : Reduction a b) (e : V ≃ W) :
    Reduction (a.rename e) (b.rename e) := by
  induction h generalizing W with
  | atomComm c x p q =>
    have hb := Agent.bind_rename e q (.var x)
    simp only [Term.subst] at hb
    have hr := Reduction.atomComm c (e x) (p.subst (fun v => .var (e v)))
      (q.subst (fun v => .var (Option.map e v)))
    rw [hb] at hr
    simpa only [rename,Agent.subst,Term.subst,liftSubst_rename] using hr
  | thenBranch f p q hf =>
    rename_i U
    have he : (f.subst (Empty.elim : Empty → Term U)).subst (fun v => Term.var (e v)) =
        f.subst (Empty.elim : Empty → Term W) := by
      rw [Formula.subst_subst]
      congr 1
      funext v; exact v.elim
    simpa only [rename,Agent.subst,he] using Reduction.thenBranch f
      (p.subst (fun v => .var (e v))) (q.subst (fun v => .var (e v))) hf
  | elseBranch f p q hf =>
    rename_i U
    have he : (f.subst (Empty.elim : Empty → Term U)).subst (fun v => Term.var (e v)) =
        f.subst (Empty.elim : Empty → Term W) := by
      rw [Formula.subst_subst]
      congr 1
      funext v; exact v.elim
    simpa only [rename,Agent.subst,he] using Reduction.elseBranch f
      (p.subst (fun v => .var (e v))) (q.subst (fun v => .var (e v))) hf
  | parLeft c h ih => exact .parLeft _ (ih e)
  | parRight c h ih => exact .parRight _ (ih e)
  | newVar h ih => exact .newVar (ih (Equiv.optionCongr e))
  | congr hs h ht ih => exact .congr (hs.rename e e.injective) (ih e) (ht.rename e e.injective)

theorem FreeStep.rename_equiv {a b : Extended V} {l : FreeLabel V}
    (h : FreeStep a l b) (e : V ≃ W) :
    FreeStep (a.rename e) (l.rename e) (b.rename e) := by
  induction h generalizing W with
  | input c m p =>
    simpa only [rename,Agent.subst,liftSubst_rename,FreeLabel.rename,Agent.bind_rename] using
      FreeStep.input c (m.subst (fun v => .var (e v))) (p.subst (fun v => .var (Option.map e v)))
  | output => exact .output _ _ _
  | scopeInput h ih =>
    apply FreeStep.scopeInput
    simpa only [FreeLabel.rename,shiftTerm_rename,Equiv.optionCongr,Equiv.coe_fn_mk] using ih (Equiv.optionCongr e)
  | scopeOutput h ih => exact .scopeOutput (ih (Equiv.optionCongr e))
  | parLeft c h ih => exact .parLeft _ (ih e)
  | parRight c h ih => exact .parRight _ (ih e)
  | congr hs h ht ih => exact .congr (hs.rename e e.injective) (ih e) (ht.rename e e.injective)

theorem rename_swapBinders (a : Extended (Option (Option V))) (σ : V → W) :
    (a.rename swapBinders).rename (Option.map (Option.map σ)) =
      (a.rename (Option.map (Option.map σ))).rename swapBinders := by
  simp only [rename_comp]
  congr 1
  funext v
  cases v with
  | none => rfl
  | some v => cases v <;> rfl

theorem BoundOutput.rename_equiv {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (e : V ≃ W) :
    BoundOutput (a.rename e) c (b.rename (Option.map e)) := by
  induction h generalizing W with
  | openAtom h => exact .openAtom (h.rename_equiv (Equiv.optionCongr e))
  | scope h ih =>
    simpa only [rename,rename_swapBinders,Equiv.optionCongr,Equiv.coe_fn_mk] using
      BoundOutput.scope (ih (Equiv.optionCongr e))
  | parLeft d h ih =>
    simpa only [rename,rename_comp,Function.comp_def,Option.map_some] using
      BoundOutput.parLeft (d.rename e) (ih e)
  | parRight d h ih =>
    simpa only [rename,rename_comp,Function.comp_def,Option.map_some] using
      BoundOutput.parRight (d.rename e) (ih e)
  | congr hs h ht ih =>
    exact .congr (hs.rename e e.injective) (ih e)
      (ht.rename (Option.map e) (option_map_injective e e.injective))

end Extended
namespace Named

theorem Reduction.rename_equiv {a b : Named V} (h : Reduction a b) (e : V ≃ W) :
    Reduction (a.rename e) (b.rename e) := by
  induction h generalizing W with
  | embed h => exact .embed (h.rename_equiv e)
  | parLeft c h ih => exact .parLeft _ (ih e)
  | parRight c h ih => exact .parRight _ (ih e)
  | newName n h ih => exact .newName n (ih e)
  | newVar h ih => exact .newVar (ih (Equiv.optionCongr e))
  | congr hs h ht ih => exact .congr (hs.rename e e.injective) (ih e) (ht.rename e e.injective)

theorem FreeStep.rename_equiv {a b : Named V} {l : Extended.FreeLabel V}
    (h : FreeStep a l b) (e : V ≃ W) :
    FreeStep (a.rename e) (l.rename e) (b.rename e) := by
  induction h generalizing W with
  | embed h => exact .embed (h.rename_equiv e)
  | scopeName n hf h ih =>
    apply FreeStep.scopeName n _ (ih e)
    cases ‹Extended.FreeLabel _› <;>
      simpa only [Extended.FreeLabel.rename,Extended.FreeLabel.nameSupport,Term.nameSupport_rename] using hf
  | scopeInput h ih =>
    apply FreeStep.scopeInput
    simpa only [Extended.FreeLabel.rename,shiftTerm_rename,Equiv.optionCongr,Equiv.coe_fn_mk] using ih (Equiv.optionCongr e)
  | scopeOutput h ih => exact .scopeOutput (ih (Equiv.optionCongr e))
  | parLeft c h ih => exact .parLeft _ (ih e)
  | parRight c h ih => exact .parRight _ (ih e)
  | congr hs h ht ih => exact .congr (hs.rename e e.injective) (ih e) (ht.rename e e.injective)

theorem BoundOutput.rename_equiv {a : Named V} {b : Named (Option V)} {c : Nat}
    (h : BoundOutput a c b) (e : V ≃ W) :
    BoundOutput (a.rename e) c (b.rename (Option.map e)) := by
  induction h generalizing W with
  | embed h => exact .embed (h.rename_equiv e)
  | openAtom h => exact .openAtom (h.rename_equiv (Equiv.optionCongr e))
  | scopeName n hf h ih => exact .scopeName n hf (ih e)
  | scopeVar h ih =>
    simpa only [rename,rename_swapBinders,Equiv.optionCongr,Equiv.coe_fn_mk] using
      BoundOutput.scopeVar (ih (Equiv.optionCongr e))
  | parLeft d h ih =>
    simpa only [rename,rename_comp,Function.comp_def,Option.map_some] using
      BoundOutput.parLeft (d.rename e) (ih e)
  | parRight d h ih =>
    simpa only [rename,rename_comp,Function.comp_def,Option.map_some] using
      BoundOutput.parRight (d.rename e) (ih e)
  | congr hs h ht ih =>
    exact .congr (hs.rename e e.injective) (ih e)
      (ht.rename (Option.map e) (option_map_injective e e.injective))

end Named
end ExplainableCrypto.Helios.Symbolic.Historical.General.Source
