import ExplainableCrypto.Helios.Symbolic.SourceCommonFramePolicy

namespace ExplainableCrypto.Helios.Symbolic
variable {V W : Type}

theorem Term.mapNames_congr (t : Term V) (f g : Nat → Nat)
    (h : ∀ n ∈ t.nameSupport, f n = g n) : t.mapNames f = t.mapNames g := by
  induction t <;> simp_all [Term.mapNames,Term.nameSupport]

namespace Historical.General.Source.Extended

/-- Equations imposed by active definitions. Plain code contributes no frame
equation; local variables existentially range over complete ground terms. -/
def Satisfies : {V : Type} → Extended V → (V → Ground) → Prop
  | _, .plain _, _ => True
  | _, .active x m, env => EqE (env x) (m.subst env)
  | _, .par a b, env => a.Satisfies env ∧ b.Satisfies env
  | _, .newVar a, env => ∃ m : Ground, a.Satisfies (extendEnv env m)

theorem frame_constraints_realizes_iff (a : Extended V) (env : V → Ground) (p : Agent Empty) :
    a.frameOf.Realizes env p ↔ a.Satisfies env ∧ Agent.EvalEq .nil p := by
  induction a generalizing p with
  | plain => simp only [frameOf,Realizes,Agent.subst,Satisfies,true_and]
  | active => rfl
  | newVar a ih => simp only [frameOf,Realizes,Satisfies,ih,exists_and_right]
  | par a b ha hb =>
    simp only [frameOf,Realizes,ha,hb,Satisfies]
    constructor
    · rintro ⟨q,r,⟨ha,hq⟩,⟨hb,hr⟩,hp⟩
      exact ⟨⟨ha,hb⟩,(Agent.EvalEq.of_parEq (Agent.ParEq.zero .nil).symm).trans
        ((Agent.EvalEq.par hq hr).trans hp)⟩
    · rintro ⟨⟨ha,hb⟩,hp⟩
      exact ⟨.nil,.nil,⟨ha,.refl _⟩,⟨hb,.refl _⟩,
        (Agent.EvalEq.of_parEq (.zero _)).trans hp⟩

theorem satisfies_iff_realizes (a : Extended V) (env : V → Ground) :
    a.Satisfies env ↔ a.frameOf.Realizes env .nil := by
  rw [frame_constraints_realizes_iff]
  exact ⟨fun h => ⟨h,.refl _⟩,And.left⟩

theorem Structural.satisfies {a b : Extended V} (h : Structural a b) (env : V → Ground) :
    a.Satisfies env ↔ b.Satisfies env := by
  rw [satisfies_iff_realizes,satisfies_iff_realizes]
  exact h.frameOf.realizes env .nil

theorem satisfies_rename (a : Extended V) (σ : V → W) (env : W → Ground) :
    (a.rename σ).Satisfies env ↔ a.Satisfies (fun v => env (σ v)) := by
  rw [satisfies_iff_realizes,frameOf_rename,realizes_rename,← satisfies_iff_realizes]

theorem satisfies_mapNames_congr (a : Extended V) (f g : Nat → Nat) (env : V → Ground)
    (h : ∀ n, SourceName.base n ∈ a.nameSupport → f n = g n) :
    (a.mapNames f id).Satisfies env ↔ (a.mapNames g id).Satisfies env := by
  induction a with
  | plain => rfl
  | active x m =>
    have hm := m.mapNames_congr f g (fun n hn => h n (Finset.mem_image.mpr ⟨n,hn,rfl⟩))
    simp only [mapNames,Satisfies,hm]
  | par a b ha hb =>
    exact and_congr (ha _ (fun n hn => h n (Finset.mem_union_left _ hn)))
      (hb _ (fun n hn => h n (Finset.mem_union_right _ hn)))
  | newVar a ih => exact exists_congr (fun m => ih _ h)

theorem satisfies_mapNames_channels (a : Extended V) (f g : Nat → Nat) (env : V → Ground) :
    (a.mapNames f g).Satisfies env ↔ (a.mapNames f id).Satisfies env := by
  induction a <;> simp_all only [mapNames,Satisfies]

theorem satisfies_frameOf (a : Extended V) (env : V → Ground) :
    a.frameOf.Satisfies env ↔ a.Satisfies env := by
  induction a <;> simp_all only [frameOf,Satisfies]

theorem activeFrame_satisfies_iff {restricted : Finset Nat} {handles : Nat}
    (φ : Frame restricted handles) (env : Fin handles → Ground) :
    (activeFrame φ).Satisfies env ↔ ∀ i, EqE (env i) (φ.value i) := by
  rw [satisfies_iff_realizes,activeFrame_frameOf,activeFrame_realizes_iff]
  exact ⟨And.left,fun h => ⟨h,.refl _⟩⟩

end Historical.General.Source.Extended
end ExplainableCrypto.Helios.Symbolic
