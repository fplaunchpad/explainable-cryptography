import ExplainableCrypto.Helios.Symbolic.SourceBinderStructure

namespace ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
variable {V : Type}

/-- Reclosing the exported variable restores the old complete frame under
original structural rules and the source's existing variable commutation. -/
theorem BoundOutput.binder_frame_reclose {a : Extended V} {b : Extended (Option V)}
    {c : Nat} (h : BoundOutput a c b) : BinderStructural (.newVar b.frameOf) a.frameOf := by
  induction h with
  | openAtom h => exact .newVar (.source h.frameOf.symm)
  | scope h ih =>
    simp only [frameOf,frameOf_rename]
    exact (BinderStructural.varComm _).symm.trans (.newVar ih)
  | parLeft d h ih =>
    simp only [frameOf,frameOf_rename]
    exact (BinderStructural.newVar (.source (.comm _ _))).trans
      ((BinderStructural.source (Structural.newPar _ _).symm).trans
        ((BinderStructural.parRight _ ih).trans (.source (.comm _ _))))
  | parRight a h ih =>
    simp only [frameOf,frameOf_rename]
    exact (BinderStructural.source (Structural.newPar _ _).symm).trans (.parRight _ ih)
  | congr ha h hb ih =>
    exact (BinderStructural.newVar (.source hb.frameOf.symm)).trans
      (ih.trans (.source ha.frameOf.symm))

/-- Rigidity is exactly retained if the newly exported handle is hidden again. -/
theorem BoundOutput.rigid_reclose {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (env : V → Ground) :
    (Extended.newVar b).Rigid env ↔ a.Rigid env := by
  have he := h.binder_frame_reclose.rigid env
  simpa only [Rigid,satisfies_frameOf,rigid_frameOf] using he

/-- An actual bound output preserves rigidity of every remaining local for
any chosen new handle value. Source rigidity cannot be inferred conversely. -/
theorem BoundOutput.rigid_target {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) {env : V → Ground} (ha : a.Rigid env) (m : Ground) :
    b.Rigid (extendEnv env m) :=
  rigid_newVar_body ((h.rigid_reclose env).mpr ha) m

/-- Arbitrary target environments split into their actual old and fresh
components; no canonical frame realization premise is needed. -/
theorem BoundOutput.rigid_all_targets {a : Extended V} {b : Extended (Option V)} {c : Nat}
    (h : BoundOutput a c b) (ha : ∀ env, a.Rigid env) (env : Option V → Ground) :
    b.Rigid env := by
  have he : extendEnv (fun v => env (some v)) (env none) = env := by funext v; cases v <;> rfl
  simpa only [he] using h.rigid_target (ha (fun v => env (some v))) (env none)

end ExplainableCrypto.Helios.Symbolic.Historical.General.Source.Extended
